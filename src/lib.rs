//! This crate implements an LRU (least-recently-used) cache that is limited by
//! the total size of its entries. As more entries are added than fit in the
//! specified memory bound, the least-recently-used ones are ejected. The cache
//! supports average-case O(1) insertion, retrieval, and removal.
//!
//! Note that the memory required for each entry is only an estimate and some
//! auxiliary structure is disregarded. With some data structures (such as the
//! [HashMap](std::collections::HashMap) or
//! [HashSet](std::collections::HashSet)), some internal data is not
//! accessible, so the required memory is even more underestimated. Therefore,
//! the actual data structure can take more memory than was assigned, however
//! this should not be an excessive amount in most cases.
//!
//! # Motivating example
//!
//! Imagine we are building a web server that sends large responses to clients.
//! To reduce the load, they are split into sections and the client is given a
//! token to access the different sections individually. However, recomputing
//! the sections on each request leads to too much server load, so they need to
//! be cached. An LRU cache is useful in this situation, as clients are most
//! likely to request new sections temporally localized.
//!
//! Now consider the situation when most responses are very small, but some may
//! be large. This would either lead to the cache being conservatively sized
//! and allow for less cached responses than would normally be possible, or to
//! the cache being liberally sized and potentially overflow memory if too many
//! large responses have to be cached. To prevent this, the cache is designed
//! with an upper bound on its memory instead of the number of elements.
//!
//! The code below shows how the basic structure might look like.
//!
//! ```
//! use lru_mem::LruCache;
//!
//! struct WebServer {
//!     cache: LruCache<u128, Vec<String>>
//! }
//!
//! fn random_token() -> u128 {
//!     // A cryptographically secure random token.
//!     42
//! }
//!
//! fn generate_sections(input: String) -> Vec<String> {
//!     // A complicated set of sections that is highly variable in size.
//!     vec![input.clone(), input]
//! }
//!
//! impl WebServer {
//!     fn new(max_size: usize) -> WebServer {
//!         // Create a new web server with a cache that holds at most max_size
//!         // bytes of elements.
//!         WebServer {
//!             cache: LruCache::new(max_size)
//!         }
//!     }
//!
//!     fn on_query(&mut self, input: String) -> u128 {
//!         // Generate sections, store them in the cache, and return token.
//!         let token = random_token();
//!         let sections = generate_sections(input);
//!         self.cache.insert(token, sections)
//!             .expect("sections do not fit in the cache");
//! 
//!         token
//!     }
//!
//!     fn on_section_request(&mut self, token: u128, index: usize)
//!             -> Option<&String> {
//!         // Lookup the token and get the section with given index.
//!         self.cache.get(&token).and_then(|s| s.get(index))
//!     }
//! }
//! ```
//!
//! For further details on how to use the cache, see the [LruCache] struct.

use hashbrown::TryReserveError;
use hashbrown::hash_map::DefaultHashBuilder;
use hashbrown::raw::RawTable;

use std::borrow::Borrow;
use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash, BuildHasher};
use std::hint;
use std::mem::{self, MaybeUninit};
use std::ptr;

mod error;
mod iter;
mod mem_size;

#[cfg(test)]
mod tests;

pub use error::{LruError, LruResult};
pub use iter::{Drain, IntoIter, Iter, Keys, Values};
pub use mem_size::MemSize;

struct Entry<K, V> {
    size: usize,
    prev: *mut Entry<K, V>,
    next: *mut Entry<K, V>,
    key: MaybeUninit<K>,
    value: MaybeUninit<V>
}

impl<K, V> Entry<K, V> {
    fn new_seal() -> Entry<K, V> {
        Entry {
            size: 0,
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
            key: MaybeUninit::uninit(),
            value: MaybeUninit::uninit()
        }
    }

    unsafe fn key(&self) -> &K {
        self.key.assume_init_ref()
    }

    unsafe fn value(&self) -> &V {
        self.value.assume_init_ref()
    }
}

impl<K: Clone, V: Clone> Entry<K, V> {
    unsafe fn clone(&self) -> Entry<K, V> {
        Entry {
            size: self.size,
            prev: self.prev,
            next: self.next,
            key: MaybeUninit::new(self.key().clone()),
            value: MaybeUninit::new(self.value().clone())
        }
    }
}

impl<K: MemSize, V: MemSize> Entry<K, V> {
    fn new(key: K, value: V) -> Entry<K, V> {
        let size = entry_size(&key, &value);

        Entry {
            size,
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
            key: MaybeUninit::new(key),
            value: MaybeUninit::new(value)
        }
    }
}

/// Gets the memory an entry with the given key and value would occupy in an
/// LRU cache, in bytes. This is also the function used internally, thus if the
/// returned number of bytes fits inside the cache (as can be determined using
/// [LruCache::current_size] and [LruCache::max_size]), it is guaranteed not to
/// eject an element.
///
/// # Arguments
///
/// * `key`: A reference to the key of the entry whose size to determine.
/// * `value`: A reference to the value of the entry whose size to determine.
///
/// # Example
///
/// ```
/// let key_1 = 0u64;
/// let value_1 = vec![0u8; 10];
/// let size_1 = lru_mem::entry_size(&key_1, &value_1);
///
/// let key_2 = 1u64;
/// let value_2 = vec![0u8; 1000];
/// let size_2 = lru_mem::entry_size(&key_2, &value_2);
///
/// assert!(size_1 < size_2);
/// ```
pub fn entry_size<K: MemSize, V: MemSize>(key: &K, value: &V) -> usize {
    let key_size = key.mem_size();
    let value_size = value.mem_size();
    let meta_size = mem::size_of::<Entry<(), ()>>();
    key_size + value_size + meta_size
}

/// An LRU (least-recently-used) cache that stores values associated with keys.
/// Insertion, retrieval, and removal all have average-case complexity in O(1).
/// The cache has an upper memory bound, which is set at construction time.
/// This is enforced using estimates on the memory requirement of each
/// key-value-pair. Note that some auxiliary data structures may allocate more
/// memory. So, this data structure may require more than the given limit.
///
/// Each time a new entry is added with [LruCache::insert], it is checked
/// whether it fits in the given memory bound. If it does not, the
/// least-recently-used element is dropped from the cache, until the new entry
/// fits.
///
/// Note that both the key type `K` and the value type `V` must implement the
/// [MemSize] trait to allow for size estimation in normal usage. In addition,
/// the key type `K` is required to implement [Hash] and [Eq] for most
/// meaningful operations.
///
/// Mutable access is not allowed directly, since it may change the size of an
/// entry. It must be done either by removing the element using
/// [LruCache::remove] and inserting it again, or passing a mutating closure to
/// [LruCache::mutate].
pub struct LruCache<K, V, S = DefaultHashBuilder> {
    table: RawTable<Entry<K, V>>,

    // The seal is a dummy entry that is simultaneously in front of the head
    // and behind the tail of the list. You can imagine it as connecting the
    // list to a cycle.
    // Having a dummy entry makes some operations (in particular unhinging)
    // simpler. The cache would also work with two dummy entries, but only the
    // next-field of the head and prev-field of the tail would be used. So, we
    // use one dummy entry to act as both. It has to be ensured that we never
    // iterate over this seal, so the edge case in which the cache is empty has
    // to be considered in every situation where we iterate over the elements.

    // This system is inspired by the lru-crate: https://crates.io/crates/lru

    seal: *mut Entry<K, V>,
    current_size: usize,
    max_size: usize,
    hash_builder: S
}

impl<K, V> LruCache<K, V> {

    /// Creates a new, empty LRU cache with the given maximum memory size.
    ///
    /// # Arguments
    ///
    /// * `max_size`: The maximum number of bytes that the sum of the memory
    /// estimates of all entries may occupy. It is important to note that this
    /// bound may be exceeded in total memory requirement of the created data
    /// structure.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// // Create an LRU cache with 16 KiB memory limit
    /// let cache: LruCache<String, String> = LruCache::new(16 * 1024);
    /// ```
    pub fn new(max_size: usize) -> LruCache<K, V> {
        LruCache::with_table_and_hasher(max_size, RawTable::new(),
            DefaultHashBuilder::new())
    }

    /// Creates a new, empty LRU cache with the given maximum memory size and
    /// the specified initial capacity.
    ///
    /// # Arguments
    ///
    /// * `max_size`: The maximum number of bytes that the sum of the memory
    /// estimates of all entries may occupy. It is important to note that this
    /// bound may be exceeded in total memory requirement of the created data
    /// structure.
    /// * `capacity`: A lower bound on the number of elements that the cache
    /// will be able to hold without reallocating.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// // Create an LRU with 4 KiB memory limit that can hold at least 8
    /// // elements without reallocating.
    /// let cache: LruCache<String, String> = LruCache::with_capacity(4096, 8);
    /// ```
    pub fn with_capacity(max_size: usize, capacity: usize) -> LruCache<K, V> {
        LruCache::with_table_and_hasher(max_size,
            RawTable::with_capacity(capacity), DefaultHashBuilder::new())
    }
}

impl<K, V, S> LruCache<K, V, S> {

    fn with_table_and_hasher(max_size: usize, table: RawTable<Entry<K, V>>,
            hash_builder: S) -> LruCache<K, V, S> {
        let seal = Box::into_raw(Box::new(Entry::new_seal()));

        unsafe {
            (*seal).next = seal;
            (*seal).prev = seal;
        }

        LruCache {
            table,
            seal,
            current_size: 0,
            max_size,
            hash_builder
        }
    }

    /// Creates a new, empty LRU cache with the given maximum memory size which
    /// will use the given hash builder to hash keys.
    ///
    /// # Arguments
    ///
    /// * `max_size`: The maximum number of bytes that the sum of the memory
    /// estimates of all entries may occupy. It is important to note that this
    /// bound may be exceeded in total memory requirement of the created data
    /// structure.
    /// * `hash_builder`: The hasher used to hash keys. It should implement the
    /// [BuildHasher] trait to allow operations being applied to the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use hashbrown::hash_map::DefaultHashBuilder;
    /// use lru_mem::LruCache;
    ///
    /// // Create an LRU with 4 KiB memory limit that uses s for hashing keys.
    /// let s = DefaultHashBuilder::default();
    /// let cache: LruCache<String, String> = LruCache::with_hasher(4096, s);
    /// ```
    pub fn with_hasher(max_size: usize, hash_builder: S) -> LruCache<K, V, S> {
        LruCache::with_table_and_hasher(max_size, RawTable::new(),
            hash_builder)
    }

    /// Creates a new, empty LRU cache with the given maximum memory size and
    /// the specified initial capacity which will use the given hash builder to
    /// hash keys.
    ///
    /// # Arguments
    ///
    /// * `max_size`: The maximum number of bytes that the sum of the memory
    /// estimates of all entries may occupy. It is important to note that this
    /// bound may be exceeded in total memory requirement of the created data
    /// structure.
    /// * `capacity`: A lower bound on the number of elements that the cache
    /// will be able to hold without reallocating.
    /// * `hash_builder`: The hasher used to hash keys. It should implement the
    /// [BuildHasher] trait to allow operations being applied to the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use hashbrown::hash_map::DefaultHashBuilder;
    /// use lru_mem::LruCache;
    ///
    /// // Create an LRU with 8 KiB memory limit that can hold at least 8
    /// // elements without reallocating that uses s for hashing keys.
    /// let s = DefaultHashBuilder::default();
    /// let cache: LruCache<String, String> =
    ///     LruCache::with_capacity_and_hasher(4096, 8, s);
    /// ```
    pub fn with_capacity_and_hasher(max_size: usize, capacity: usize,
            hash_builder: S) -> LruCache<K, V, S> {
        LruCache::with_table_and_hasher(max_size,
            RawTable::with_capacity(capacity), hash_builder)
    }

    /// Gets the maximum number of bytes that the sum of the memory estimates
    /// of all entries may occupy. It is important to note that this bound may
    /// be exceeded in total memory requirement of the created data structure.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let cache: LruCache<String, String> = LruCache::new(65536);
    /// assert_eq!(65536, cache.max_size());
    /// ```
    pub fn max_size(&self) -> usize {
        self.max_size
    }

    /// Gets the current estimated memory of all entries contained in this
    /// cache, in bytes.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache: LruCache<String, String> = LruCache::new(1024);
    /// assert_eq!(0, cache.current_size());
    ///
    /// // The exact amount of occupied memory depends not only on the values,
    /// // but also some auxiliary data of the internal structures.
    /// cache.insert("hello".to_owned(), "world".to_owned()).unwrap();
    /// assert!(cache.current_size() > 0);
    /// ```
    pub fn current_size(&self) -> usize {
        self.current_size
    }

    /// Gets the number of entries contained in this cache.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache: LruCache<String, String> = LruCache::new(1024);
    /// assert_eq!(0, cache.len());
    ///
    /// cache.insert("apple".to_owned(), "banana".to_owned()).unwrap();
    /// assert_eq!(1, cache.len());
    /// ```
    pub fn len(&self) -> usize {
        self.table.len()
    }

    /// Indicates whether this cache is empty, i.e. its length
    /// ([LruCache::len]) is zero.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache: LruCache<String, String> = LruCache::new(1024);
    /// assert!(cache.is_empty());
    ///
    /// cache.insert("apple".to_owned(), "banana".to_owned()).unwrap();
    /// assert!(!cache.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements the cache can hold without reallocating.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache: LruCache<String, String> =
    ///     LruCache::with_capacity(1024, 10);
    /// assert!(cache.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.table.capacity()
    }

    /// Creates an iterator over the entries (keys and values) contained in
    /// this cache, ordered from least- to most-recently-used. The values are
    /// not touched, i.e. the usage history is not altered in any way. That is,
    /// the semantics are as in [LruCache::peek].
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    /// cache.insert("grapefruit".to_owned(), "bitter".to_owned()).unwrap();
    /// let mut iter = cache.iter();
    ///
    /// assert_eq!(Some((&"apple".to_owned(), &"sweet".to_owned())),
    ///     iter.next());
    /// assert_eq!(Some((&"grapefruit".to_owned(), &"bitter".to_owned())),
    ///     iter.next_back());
    /// assert_eq!(Some((&"lemon".to_owned(), &"sour".to_owned())),
    ///     iter.next());
    /// assert_eq!(None, iter.next());
    /// assert_eq!(None, iter.next_back());
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::new(self)
    }

    /// Creates an iterator over the keys contained in this cache, ordered from
    /// least- to most-recently-used. The values are not touched, i.e. the
    /// usage history is not altered in any way. That is, the semantics are as
    /// in [LruCache::peek].
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    /// cache.insert("grapefruit".to_owned(), "bitter".to_owned()).unwrap();
    /// let mut keys = cache.keys();
    ///
    /// assert_eq!(Some(&"apple".to_owned()), keys.next());
    /// assert_eq!(Some(&"grapefruit".to_owned()), keys.next_back());
    /// assert_eq!(Some(&"lemon".to_owned()), keys.next());
    /// assert_eq!(None, keys.next());
    /// assert_eq!(None, keys.next_back());
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys::new(self)
    }

    /// Creates an iterator over the values contained in this cache, ordered
    /// from least- to most-recently-used. The values are not touched, i.e. the
    /// usage history is not altered in any way. That is, the semantics are as
    /// in [LruCache::peek].
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    /// cache.insert("grapefruit".to_owned(), "bitter".to_owned()).unwrap();
    /// let mut values = cache.values();
    ///
    /// assert_eq!(Some(&"sweet".to_owned()), values.next());
    /// assert_eq!(Some(&"bitter".to_owned()), values.next_back());
    /// assert_eq!(Some(&"sour".to_owned()), values.next());
    /// assert_eq!(None, values.next());
    /// assert_eq!(None, values.next_back());
    /// ```
    pub fn values(&self) -> Values<'_, K, V> {
        Values::new(self)
    }
}

fn make_hash<K, Q, S>(hash_builder: &S, val: &Q) -> u64
where
    K: Borrow<Q>,
    Q: Hash + ?Sized,
    S: BuildHasher,
{
    use core::hash::Hasher;
    let mut state = hash_builder.build_hasher();
    val.hash(&mut state);
    state.finish()
}

fn make_insert_hash<K, S>(hash_builder: &S, val: &K) -> u64
where
    K: Hash,
    S: BuildHasher,
{
    use core::hash::Hasher;
    let mut state = hash_builder.build_hasher();
    val.hash(&mut state);
    state.finish()
}

fn make_hasher<K, V, S>(hash_builder: &S) -> impl Fn(&Entry<K, V>) -> u64 + '_
where
    K: Hash,
    S: BuildHasher
{
    move |val| make_hash::<K, K, S>(hash_builder, unsafe { val.key() })
}

fn equivalent_key<Q, K, V>(k: &Q) -> impl Fn(&Entry<K, V>) -> bool + '_
where
    K: Borrow<Q>,
    Q: ?Sized + Eq,
{
    move |x| k.eq(unsafe { x.key() }.borrow())
}

impl<K, V, S> LruCache<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher
{
    fn remove_from_table<Q>(&mut self, key: &Q) -> Option<Entry<K, V>>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized
    {
        let hash = make_hash::<K, Q, S>(&self.hash_builder, key);
        self.table.remove_entry(hash, equivalent_key(key))
    }

    fn get_from_table<Q>(&self, key: &Q) -> Option<&Entry<K, V>>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized
    {
        let hash = make_hash::<K, Q, S>(&self.hash_builder, key);
        self.table.get(hash, equivalent_key(key))
    }

    fn get_mut_from_table<Q>(&mut self, key: &Q) -> Option<&mut Entry<K, V>>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized
    {
        let hash = make_hash::<K, Q, S>(&self.hash_builder, key);
        self.table.get_mut(hash, equivalent_key(key))
    }

    #[inline]
    fn insert_into_table_with_hash(&mut self, hash: u64, entry: Entry<K, V>)
            -> Result<*mut Entry<K, V>, Entry<K, V>> {
        match self.table.try_insert_no_grow(hash, entry) {
            Ok(bucket) => Ok(bucket.as_ptr()),
            Err(entry) => Err(entry)
        }
    }

    /// Assumes that there is no entry with the same key in the table. If
    /// insertion works, returns a pointer to the entry inside the table.
    /// Otherwise, returns the entry input into this function.
    fn insert_into_table(&mut self, entry: Entry<K, V>)
            -> Result<*mut Entry<K, V>, Entry<K, V>> {
        let key = unsafe { entry.key.assume_init_ref() };
        let hash = make_insert_hash::<K, S>(&self.hash_builder, key);

        self.insert_into_table_with_hash(hash, entry)
    }

    #[inline]
    unsafe fn unhinge(&mut self, entry: &Entry<K, V>) {
        let prev = entry.prev;
        let next = entry.next;

        (*prev).next = next;
        (*next).prev = prev;
    }

    unsafe fn set_head(&mut self, entry: *mut Entry<K, V>) {
        let next = (*self.seal).next;
        (*entry).next = next;
        (*entry).prev = self.seal;
        (*next).prev = entry;
        (*self.seal).next = entry;
    }

    unsafe fn touch_ptr(&mut self, entry: *mut Entry<K, V>) {
        self.unhinge(&*entry);
        self.set_head(entry);
    }

    fn remove_metadata(&mut self, entry: Entry<K, V>) -> (K, V) {
        unsafe {
            self.unhinge(&entry);
            self.current_size -= entry.size;
            (entry.key.assume_init(), entry.value.assume_init())
        }
    }

    #[inline]
    unsafe fn remove_ptr(&mut self, entry: *mut Entry<K, V>) -> (K, V) {
        let entry = self.remove_from_table((*entry).key()).unwrap();
        self.remove_metadata(entry)
    }

    fn eject_to_target(&mut self, target: usize) {
        while self.current_size > target {
            self.remove_lru();
        }
    }

    fn insert_untracked(&mut self, entry: Entry<K, V>) {
        let entry_ptr = self.insert_into_table(entry)
            .unwrap_or_else(|_| unsafe { hint::unreachable_unchecked() });
        unsafe { self.set_head(entry_ptr) };
    }

    fn reallocate_with<F, R>(&mut self, reserve: F) -> R
    where
        F: FnOnce(&mut Self) -> R
    {
        let mut entries = Vec::with_capacity(self.len());
        let mut tail = unsafe { (*self.seal).prev };

        while tail != self.seal {
            entries.push(unsafe { ptr::read(tail) });
            tail = unsafe { (*tail).prev };
        }

        self.table.clear_no_drop();
        let result = reserve(self);

        unsafe {
            (*self.seal).next = self.seal;
            (*self.seal).prev = self.seal;
        }

        for entry in entries {
            self.insert_untracked(entry);
        }

        result
    }

    fn reallocate(&mut self, new_capacity: usize) {
        self.reallocate_with(|this|
            this.table.reserve(new_capacity, make_hasher(&this.hash_builder)))
    }

    fn lru_ptr(&self) -> Option<*mut Entry<K, V>> {
        let lru = unsafe { (*self.seal).prev };

        if lru == self.seal {
            None
        }
        else {
            Some(lru)
        }
    }

    fn mru_ptr(&self) -> Option<*mut Entry<K, V>> {
        let mru = unsafe { (*self.seal).next };

        if mru == self.seal {
            None
        }
        else {
            Some(mru)
        }
    }

    /// Removes the least-recently-used value from this cache. This returns
    /// both key and value of the removed value. If this cache is empty, `None`
    /// is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    ///
    /// assert_eq!(Some(("apple".to_owned(), "sweet".to_owned())),
    ///     cache.remove_lru());
    /// assert_eq!(1, cache.len());
    /// ```
    pub fn remove_lru(&mut self) -> Option<(K, V)> {
        self.lru_ptr().map(|ptr| unsafe { self.remove_ptr(ptr) })
    }

    /// Gets a reference to the least-recently-used entry from this cache. This
    /// returns both key and value of the entry. If the cache is empty, `None`
    /// is returned.
    ///
    /// This method also marks the value as most-recently-used. If you want the
    /// usage history to not be updated, use [LruCache::peek_lru] instead.
    ///
    /// The memory requirement of the value may not be changed.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    ///
    /// assert_eq!(Some((&"apple".to_owned(), &"sweet".to_owned())),
    ///     cache.get_lru());
    /// assert_eq!(Some((&"lemon".to_owned(), &"sour".to_owned())),
    ///     cache.get_lru());
    /// ```
    pub fn get_lru(&mut self) -> Option<(&K, &V)> {
        self.lru_ptr().map(|entry| {
            unsafe {
                self.touch_ptr(entry);
                ((*entry).key(), (*entry).value())
            }
        })
    }

    /// Gets a reference to the least-recently-used entry from this cache. This
    /// returns both key and value of the entry. If the cache is empty, `None`
    /// is returned.
    ///
    /// This method does not mark the value as most-recently-used. If you want
    /// the usage history to be updated, use [LruCache::get_lru] instead.
    ///
    /// The memory requirement of the value may not be changed.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    ///
    /// assert_eq!(Some((&"apple".to_owned(), &"sweet".to_owned())),
    ///     cache.peek_lru());
    /// assert_eq!(Some((&"apple".to_owned(), &"sweet".to_owned())),
    ///     cache.peek_lru());
    /// ```
    pub fn peek_lru(&self) -> Option<(&K, &V)> {
        self.lru_ptr().map(|ptr|
            unsafe { ((*ptr).key(), (*ptr).value()) })
    }

    /// Removes the most-recently-used value from the cache. This returns both
    /// key and value of the removed entry. If the cache is empty, `None` is
    /// returned.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    ///
    /// assert_eq!(Some(("lemon".to_owned(), "sour".to_owned())),
    ///     cache.remove_mru());
    /// assert_eq!(1, cache.len());
    /// ```
    pub fn remove_mru(&mut self) -> Option<(K, V)> {
        self.mru_ptr().map(|ptr| unsafe { self.remove_ptr(ptr) })
    }

    /// Gets a reference to the most-recently-used entry from this cache. This
    /// returns both key and value of the entry. If the cache is empty, `None`
    /// is returned.
    ///
    /// Note that, for the most-recently-used entry, it does not matter whether
    /// the usage history is updated, since it was most-recently-used before.
    /// So, there is no need for a `get_mru` method.
    ///
    /// The memory requirement of the value may not be changed.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    ///
    /// assert_eq!(Some((&"lemon".to_owned(), &"sour".to_owned())),
    ///     cache.peek_mru());
    /// ```
    pub fn peek_mru(&self) -> Option<(&K, &V)> {
        self.mru_ptr().map(|ptr|
            unsafe { ((*ptr).key(), (*ptr).value()) })
    }

    fn new_capacity(&self, additional: usize)
            -> Result<usize, TryReserveError> {
        self.len().checked_add(additional)
            .ok_or_else(|| TryReserveError::CapacityOverflow)
    }

    /// Reserves capacity for at least `additional` new entries to be inserted
    /// into the cache. The collection may reserve more space to avoid frequent
    /// reallocations.
    ///
    /// # Arguments
    ///
    /// * `additional`: The number of new entries beyond the ones already
    /// contained in the cache for which space should be reserved.
    ///
    /// # Panics
    ///
    /// If the new allocation size overflows [usize].
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache: LruCache<String, String> = LruCache::new(1024);
    /// cache.insert("key".to_owned(), "value".to_owned()).unwrap();
    /// cache.reserve(10);
    /// assert!(cache.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        let new_capacity = self.new_capacity(additional).unwrap();

        if self.capacity() < new_capacity {
            self.reallocate(new_capacity);
        }
    }

    /// Tries to reserve capacity for at least `additional` new entries to be
    /// inserted into the cache. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Arguments
    ///
    /// * `additional`: The number of new entries beyond the ones already
    /// contained in the cache for which space should be reserved.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports an error, then an
    /// error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache: LruCache<String, String> = LruCache::new(1024);
    /// cache.insert("key".to_owned(), "value".to_owned()).unwrap();
    /// cache.try_reserve(10).expect("out of memory");
    /// assert!(cache.capacity() >= 11);
    /// ```
    pub fn try_reserve(&mut self, additional: usize)
            -> Result<(), TryReserveError> {
        let new_capacity = self.new_capacity(additional)?;

        if self.capacity() < new_capacity {
            self.reallocate_with(|this|
                this.table.try_reserve(new_capacity,
                    make_hasher(&this.hash_builder)))
        }
        else {
            Ok(())
        }
    }

    /// Shrinks the capacity of the cache with a lower bound. The capacity will
    /// remain at least as large as both the [length](LruCache::len) and the
    /// given lower bound while maintaining internal constraints of the hash
    /// table.
    ///
    /// If the capacity is less than the given lower bound, this method is
    /// no-op.
    ///
    /// # Arguments
    ///
    /// * `min_capacity`: A lower bound on the capacity after the operation.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache: LruCache<String, String> =
    ///     LruCache::with_capacity(1024, 10);
    /// assert!(cache.capacity() >= 10);
    /// cache.shrink_to(5);
    /// assert!(cache.capacity() >= 5);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        let new_capacity = self.len().max(min_capacity);

        if self.capacity() > new_capacity {
            self.reallocate_with(|this|
                this.table.shrink_to(new_capacity,
                    make_hasher(&this.hash_builder)))
        }
    }

    /// Shrinks the capacity of the cache as much as possible. It will drop
    /// down as much as possible while maintaining internal constraints of the
    /// hash table.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache: LruCache<String, String> =
    ///     LruCache::with_capacity(1024, 10);
    /// cache.insert("key".to_owned(), "value".to_owned()).unwrap();
    /// cache.shrink_to_fit();
    /// assert!(cache.capacity() >= 1);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(0)
    }

    /// Sets a new memory limit for this cache. If this is below the current
    /// size (see [LruCache::current_size]), the least-recently-used element
    /// will be repeatedly ejected until the limit is satisfied.
    ///
    /// Note that reducing the memory limit to a small fraction of the previous
    /// maximum may lead to large amounts of unused capacity in the underlying
    /// data structure. If this is a problem, use [LruCache::shrink_to] or
    /// [LruCache::shrink_to_fit] to avoid this.
    ///
    /// # Arguments
    ///
    /// * `max_size`: The new maximum number of bytes that the sum of the
    /// memory estimates of all entries may occupy.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    /// cache.set_max_size(cache.current_size() - 1);
    ///
    /// assert_eq!(1, cache.len());
    /// assert!(cache.max_size() < 1024);
    /// ```
    pub fn set_max_size(&mut self, max_size: usize) {
        self.eject_to_target(max_size);
        self.max_size = max_size;
    }

    /// Sets the entry with the given key as most-recently-used, i.e. all other
    /// entries currently contained in the cached will be dropped beore this
    /// one (unless others are touched/used afterwards). If there is no value
    /// associated with the given key, this method is no-op.
    ///
    /// # Arguments
    ///
    /// * `key`: The key of the entry to touch.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    /// cache.touch(&"apple".to_owned());
    ///
    /// assert_eq!(Some(("lemon".to_owned(), "sour".to_owned())),
    ///     cache.remove_lru());
    /// ```
    pub fn touch<Q>(&mut self, key: &Q)
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized
    {
        if let Some(entry) = self.get_mut_from_table(key) {
            let entry_ptr = entry as *mut Entry<K, V>;
            unsafe { self.touch_ptr(entry_ptr); }
        }
    }

    /// Gets a reference to the value associated with the given key. If there
    /// is no value for that key, `None` is returned.
    ///
    /// This method also marks the value as most-recently-used (see
    /// [LruCache::touch]). If you do not want the usage history to be updated,
    /// use [LruCache::peek] instead.
    ///
    /// The memory requirement of the value may not be changed.
    ///
    /// # Arguments
    ///
    /// * `key`: The key of the value to get.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    ///
    /// assert_eq!(Some(&"sweet".to_owned()), cache.get("apple"));
    /// assert_eq!(Some(("lemon".to_owned(), "sour".to_owned())),
    ///     cache.remove_lru());
    /// ```
    pub fn get<Q>(&mut self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized
    {
        if let Some(entry) = self.get_mut_from_table(key) {
            let entry_ptr = entry as *mut Entry<K, V>;
            unsafe { self.touch_ptr(entry_ptr); }
            Some(unsafe { (*entry_ptr).value() })
        }
        else {
            None
        }
    }

    /// Gets a reference to the value associated with the given key. If there
    /// is no value for that key, `None` is returned.
    ///
    /// This method does not mark the value as most-recently-used. If you want
    /// the usage history to be updated, use [LruCache::get] instead.
    ///
    /// The memory requirement of the value may not be changed.
    ///
    /// # Arguments
    ///
    /// * `key`: The key of the value to peek.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    ///
    /// assert_eq!(Some(&"sweet".to_owned()), cache.peek("apple"));
    /// assert_eq!(Some(("apple".to_owned(), "sweet".to_owned())),
    ///     cache.remove_lru());
    /// ```
    pub fn peek<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized
    {
        self.get_from_table(key).map(|e| unsafe { e.value() })
    }

    /// Indicates whether this cache contains an entry associated with the
    /// given key. If there is one, it is _not_ marked as most-recently-used.
    ///
    /// # Arguments
    ///
    /// * `key`: The key of the value to search.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    ///
    /// assert!(cache.contains("apple"));
    /// assert!(!cache.contains("banana"));
    /// ```
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized
    {
        let hash = make_hash::<K, Q, S>(&self.hash_builder, key);
        self.table.find(hash, equivalent_key(key)).is_some()
    }

    /// Removes the entry associated with the given key from this cache. If the
    /// cache does not contain the given key, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `key`: The key of the value to remove.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.remove("apple");
    ///
    /// assert_eq!(0, cache.len());
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized
    {
        self.remove_from_table(key).map(|entry| self.remove_metadata(entry))
    }

    /// Removes and returns the value associated with the given key from this
    /// cache. If there is no such value, `None` is returned.
    ///
    /// # Argument
    ///
    /// * `key`: The key of the value to remove.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    ///
    /// assert_eq!(Some("sour".to_owned()), cache.remove("lemon"));
    /// assert_eq!(1, cache.len());
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized
    {
        self.remove_entry(key).map(|(_, v)| v)
    }

    /// Removes all elements from this cache.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    /// cache.clear();
    ///
    /// assert_eq!(None, cache.get("lemon"));
    /// assert_eq!(0, cache.len());
    /// assert_eq!(0, cache.current_size());
    /// ```
    pub fn clear(&mut self) {
        self.table.clear();
        self.current_size = 0;
    }

    /// Creates an iterator that drains entries from this cache. Both key and
    /// value of each entry are returned. The cache is cleared afterward.
    ///
    /// Note it is important for the drain to be dropped in order to ensure
    /// integrity of the data structure. Preventing it from being dropped, e.g.
    /// using [mem::forget], can result in unexpected behavior of the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    /// cache.insert("grapefruit".to_owned(), "bitter".to_owned()).unwrap();
    /// let mut vec = cache.drain().collect::<Vec<_>>();
    ///
    /// assert_eq!(&("apple".to_owned(), "sweet".to_owned()), &vec[0]);
    /// assert_eq!(&("lemon".to_owned(), "sour".to_owned()), &vec[1]);
    /// assert_eq!(&("grapefruit".to_owned(), "bitter".to_owned()), &vec[2]);
    /// assert!(cache.is_empty());
    /// ```
    pub fn drain(&mut self) -> Drain<'_, K, V, S> {
        Drain::new(self)
    }
}

impl<K, V, S> LruCache<K, V, S>
where
    K: Eq + Hash + MemSize,
    V: MemSize,
    S: BuildHasher
{
    /// Inserts a new entry into this cache. This is initially the
    /// most-recently-used entry. If there was an entry with the given key
    /// before, it is removed and its value returned. Otherwise, `None` is
    /// returned.
    ///
    /// If you want to know before calling this method whether elements would
    /// be ejected, you can use [entry_size] to obtain the memory usage that
    /// would be assigned to the created entry and check using
    /// [LruCache::current_size] and [LruCache::max_size] whether it fits.
    ///
    /// # Arguments
    ///
    /// * `key`: The key by which the inserted entry will be identified.
    /// * `value`: The value to store in the inserted entry.
    ///
    /// # Errors
    ///
    /// Raises an [LruError::EntryTooLarge] if the entry alone would already be
    /// too large to fit inside the cache's size limit. That is, even if all
    /// other entries were ejected, it still would not be able to be inserted.
    /// If this occurs, the entry was not inserted.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    ///
    /// assert_eq!(2, cache.len());
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> LruResult<Option<V>, K, V> {
        let mut entry = Entry::new(key, value);

        if entry.size > self.max_size {
            let key = unsafe { entry.key.assume_init() };
            let value = unsafe { entry.value.assume_init() };

            return Err(LruError::EntryTooLarge {
                key,
                value,
                entry_size: entry.size,
                max_size: self.max_size
            });
        }

        // Deduplicate keys, make space

        let key = unsafe { entry.key() };
        let hash = make_insert_hash::<K, S>(&self.hash_builder, key);
        let result = self.table.remove_entry(hash, equivalent_key(key))
            .map(|e| self.remove_metadata(e).1);
        self.eject_to_target(self.max_size - entry.size);

        // Insert entry at head of list

        let size = entry.size;

        loop {
            match self.insert_into_table_with_hash(hash, entry) {
                Ok(entry_ptr) => {
                    self.current_size += size;
                    unsafe { self.set_head(entry_ptr) };
                    return Ok(result);
                },
                Err(returned_entry) => {
                    entry = returned_entry;
                    self.reallocate(self.table.capacity() * 2 + 1);
                }
            }
        }
    }

    /// Applies a mutating function to the value associated with the given key.
    /// The result of that function is returned. If there is no value for the
    /// given key, `None` is returned, and the operation is never called.
    /// Otherwise, the entry is marked as most-recently-used by this method.
    ///
    /// Note that the operation may also change the size of the value. After it
    /// terminates, the internal sizes are updated and, if necessary,
    /// least-recently-used entries are ejected to restore the memory
    /// requirement. If the operation increases the size beyond the limit of
    /// this cache, an error is raised (see below).
    ///
    /// # Arguments
    ///
    /// * `key`: The key of the value to mutate.
    /// * `op`: An operation that takes as input a mutable reference to the
    /// value, mutates it, and returns the desired result. This is forwarded by
    /// this method to the caller.
    ///
    /// # Errors
    ///
    /// Raises an [LruError::EntryTooLarge] if the operation expanded the value
    /// so much that the entry no longer fit inside the memory limit of the
    /// cache. If that is the case, the entry is removed and its parts returned
    /// in the error data.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::LruCache;
    ///
    /// let mut cache = LruCache::new(1024);
    /// cache.insert("apple".to_owned(), "sweet".to_owned()).unwrap();
    /// cache.insert("lemon".to_owned(), "sour".to_owned()).unwrap();
    ///
    /// assert_eq!(Ok(Some(())),
    ///     cache.mutate("apple", |s| s.push_str(" and sour")));
    /// assert_eq!(Some(&"sweet and sour".to_owned()), cache.peek("apple"));
    /// ```
    pub fn mutate<Q, R, F>(&mut self, key: &Q, op: F)
        -> LruResult<Option<R>, K, V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
        F: FnOnce(&mut V) -> R
    {
        let max_size = self.max_size;

        if let Some(entry) = self.get_mut_from_table(key) {
            let new_value_size;
            let result;
            let old_value_size;

            unsafe {
                old_value_size = entry.value().mem_size();
                result = op(entry.value.assume_init_mut());
                new_value_size = entry.value().mem_size();
            }

            if new_value_size > old_value_size {
                // The operation was expanding; we must ensure it still fits.

                let diff = new_value_size - old_value_size;
                let new_entry_size = entry.size + diff;

                if new_entry_size > max_size {
                    // The entry is too large after the operation; eject it and
                    // raise according error.

                    let (key, value) = self.remove_entry(key).unwrap();

                    return Err(LruError::EntryTooLarge {
                        key,
                        value,
                        entry_size: new_entry_size,
                        max_size
                    });
                }

                entry.size = new_entry_size;
                let entry_ptr = entry as *mut Entry<K, V>;
                self.current_size += diff;
                unsafe { self.touch_ptr(entry_ptr); }
                self.eject_to_target(max_size);
            }
            else {
                // The operation was non-expanding; everything is ok.

                let diff = old_value_size - new_value_size;
                entry.size -= diff;
                let entry_ptr = entry as *mut Entry<K, V>;
                self.current_size -= diff;
                unsafe { self.touch_ptr(entry_ptr); }
            }

            Ok(Some(result))
        }
        else {
            Ok(None)
        }
    }
}

impl<K, V, S> IntoIterator for LruCache<K, V, S> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, S>;

    fn into_iter(self) -> IntoIter<K, V, S> {
        IntoIter::new(self)
    }
}

impl<K, V, S> Clone for LruCache<K, V, S>
where
    K: Clone + Eq + Hash,
    V: Clone,
    S: BuildHasher + Clone
{
    fn clone(&self) -> LruCache<K, V, S> {
        let max_size = self.max_size;
        let capacity = self.capacity();
        let hash_builder = self.hash_builder.clone();
        let mut clone = LruCache::with_capacity_and_hasher(
            max_size, capacity, hash_builder);
        clone.current_size = self.current_size;
        let mut next = unsafe { (*self.seal).prev };

        while next != self.seal {
            let entry = unsafe { (&*next).clone() };
            next = entry.prev;
            clone.insert_untracked(entry);
        }

        clone
    }
}

impl<K, V, S> Drop for LruCache<K, V, S> {
    fn drop(&mut self) {
        for mut entry in self.table.drain() {
            unsafe {
                ptr::drop_in_place(entry.key.as_mut_ptr());
                ptr::drop_in_place(entry.value.as_mut_ptr());
            }
        }

        unsafe {
            let _ = Box::from_raw(self.seal);
        }
    }
}

impl<K: Debug, V: Debug, S> Debug for LruCache<K, V, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

// Since the LruCache contains raw pointers, it is not automatically marked as
// Send and Sync. We will provide manual implementations as well as arguments
// why that is ok.

// It is implicitly assumed that every LruCache only contains pointers to
// memory that belongs to the cache itself. So, if an LruCache is sent to
// another thread, that memory can now only be accessed by that thread. In
// other words, two LruCaches or anything related (e.g. iterators) can never
// access the same memory. Therefore, sending them is no issue.

unsafe impl<K: Send, V: Send, S: Send> Send for LruCache<K, V, S> { }

// If an immutable reference to an LruCache exists, there is simultaneously no
// mutable reference to the same cache. By design of the cache, any operations
// applied to that reference will allow no writing access to any of its memory.
// Those that yield any possibility of writing, such as cloning, are restricted
// to newly allocated memory. Therefore, sending references is no issue, and by
// definition of Sync, LruCache may implement it.

unsafe impl<K: Sync, V: Sync, S: Sync> Sync for LruCache<K, V, S> { }
