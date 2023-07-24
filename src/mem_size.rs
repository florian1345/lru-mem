use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, BinaryHeap};
use std::collections::hash_map::RandomState;
use std::ffi::{CStr, CString, OsStr, OsString};
use std::fmt::Alignment;
use std::marker::{PhantomData, PhantomPinned};
use std::mem;
use std::net::{
    IpAddr,
    Ipv4Addr,
    Ipv6Addr,
    Shutdown,
    SocketAddr,
    SocketAddrV4,
    SocketAddrV6
};
use std::num::{
    NonZeroI8,
    NonZeroI16,
    NonZeroI32,
    NonZeroI64,
    NonZeroI128,
    NonZeroIsize,
    NonZeroU8,
    NonZeroU16,
    NonZeroU32,
    NonZeroU64,
    NonZeroU128,
    NonZeroUsize, Wrapping
};
use std::ops::{
    Range,
    RangeFrom,
    RangeFull,
    RangeInclusive,
    RangeTo,
    RangeToInclusive
};
use std::path::{Path, PathBuf};
use std::sync::{Mutex, RwLock};
use std::thread::ThreadId;
use std::time::{Duration, Instant};

/// A trait for types whose size on the heap can be determined at runtime. Note
/// for all [Sized] types, it is sufficient to implement this trait, as a
/// blanket implementation of [MemSize] is already provided. The latter is
/// required for the [LruCache](crate::LruCache) to track the size of its
/// entries. It has implementations for most common data types and containers.
///
/// Note that reference-counting smart pointers deliberately do not implement
/// this trait, as it is not clear whether a pointer will drop the referenced
/// content when it is ejected from the cache.
///
/// # Example
///
/// For simple types which are stored completely in one memory location, such
/// as primitive types or structs of such types, it usually suffices to
/// implement this as a constant 0.
///
/// ```
/// use lru_mem::HeapSize;
/// use std::mem;
///
/// struct Vector2f {
///     x: f32,
///     y: f32
/// }
///
/// impl HeapSize for Vector2f {
///     fn heap_size(&self) -> usize {
///         0
///     }
/// }
/// ```
///
/// For more complicated types, it may be necessary to account for any
/// referenced data that is owned by the instance. If the memory is owned by
/// some field, which already implements `HeapSize`, you can rely on that
/// implementation to estimate the required heap memory. See below for an
/// example of this.
///
/// ```
/// use lru_mem::HeapSize;
///
/// struct Person {
///     name: String,
///     address: String
/// }
///
/// impl HeapSize for Person {
///     fn heap_size(&self) -> usize {
///         // Both members may have allocated data, which is accounted for by
///         // calling heap_size.
///         self.name.heap_size() + self.address.heap_size()
///     }
/// }
/// ```
///
/// In case the previous examples do not apply, consider the implementation on
/// [String] provided by this library. It demonstrates how to manually account
/// for any owned referenced data.
///
/// ```ignore
/// use lru_mem::HeapSize;
/// use std::mem;
///
/// impl HeapSize for String {
///     fn heap_size(&self) -> usize {
///         // The number of bytes reserved on the heap for UTF-8 data.
///         self.capacity()
///     }
/// }
/// ```
pub trait HeapSize {

    /// The size of the referenced data that is owned by this value in bytes,
    /// usually allocated on the heap (such as the value of a [Box] or the
    /// elements and reserved memory of a [Vec]).
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::HeapSize;
    ///
    /// assert_eq!(0, 1u64.heap_size());
    /// assert_eq!(12, "hello world!".to_owned().heap_size());
    /// ```
    fn heap_size(&self) -> usize;

    /// The total sum of the sizes of referenced data that is owned by a value
    /// in an iterator constructed with the given constructor, in bytes. This is
    /// default-implemented by computing [HeapSize::heap_size] on every element
    /// and summing them. In some cases, specialized implementations may be more
    /// performant. This is common for types which do not allocate any memory at
    /// all, where this function can be implemented by a constant zero.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::HeapSize;
    ///
    /// let boxes: [Box<i32>; 3] = [Box::new(1), Box::new(2), Box::new(3)];
    /// assert_eq!(8, Box::<i32>::heap_size_sum_iter(|| boxes.iter().filter(|item| ***item > 1)));
    /// ```
    fn heap_size_sum_iter<'item, Fun, Iter>(make_iter: Fun) -> usize
    where
        Self: 'item,
        Fun: Fn() -> Iter,
        Iter: Iterator<Item = &'item Self>
    {
        make_iter().map(HeapSize::heap_size).sum()
    }

    /// The total sum of the sizes of referenced data that is owned by a value
    /// in an exact-size-iterator constructed with the given constructor, in
    /// bytes. This is default-implemented by using
    /// [HeapSize::heap_size_sum_iter]. In some cases, specialized
    /// implementations relying on the iterator's size may be more performant.
    /// This is common for types which allocate a constant amount of memory,
    /// where this function can multiply the iterator's length.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::HeapSize;
    ///
    /// let boxes: [Box<i32>; 3] = [Box::new(1), Box::new(2), Box::new(3)];
    ///
    /// assert_eq!(12, Box::<i32>::heap_size_sum_exact_size_iter(|| boxes.iter()));
    /// ```
    fn heap_size_sum_exact_size_iter<'item, Fun, Iter>(make_iter: Fun) -> usize
    where
        Self: 'item,
        Fun: Fn() -> Iter,
        Iter: ExactSizeIterator<Item = &'item Self>
    {
        Self::heap_size_sum_iter(make_iter)
    }
}

/// A trait for types whose value size can be determined at runtime. This only
/// refers to the size of the value itself, not allocated data. For [Sized]
/// types, this is equivalent to [mem::size_of], which is provided by a blanket
/// implementation. For unsized types, [mem::size_of_val] can be used.
///
/// # Example
///
/// ```
/// use lru_mem::ValueSize;
/// use std::mem;
///
/// // unsized type
/// struct FlaggedBytes {
///     flag: bool,
///     bytes: [u8]
/// }
///
/// impl ValueSize for FlaggedBytes {
///     fn value_size(&self) -> usize {
///         // This is a valid implementation for all unsized types
///         mem::size_of_val(self)
///     }
/// }
/// ```
pub trait ValueSize {

    /// The size of this value in bytes, excluding allocated data.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::ValueSize;
    /// use std::mem;
    ///
    /// let boxed = Box::new([0u8; 64]);
    ///
    /// assert_eq!(mem::size_of::<*const ()>(), boxed.value_size());
    /// ```
    fn value_size(&self) -> usize;

    /// The total sum of the sizes of all values in the given iterator, in
    /// bytes. This is default-implemented by computing [ValueSize::value_size]
    /// on every element and summing them. For [Sized] types, a more potentially
    /// efficient implementation using [Iterator::count] is provided. If you are
    /// implementing this trait manually, it is unlikely to be more efficient to
    /// provide a manual implementation here.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::ValueSize;
    ///
    /// let nums: [i32; 3] = [1, 2, 3];
    ///
    /// assert_eq!(8, i32::value_size_sum_iter(nums.iter().filter(|item| **item > 1)));
    /// ```
    fn value_size_sum_iter<'item>(iterator: impl Iterator<Item = &'item Self>) -> usize
    where
        Self: 'item
    {
        iterator.map(ValueSize::value_size).sum()
    }

    /// The total sum of the sizes of all values in the given
    /// exact-size-iterator, in bytes. This is default-implemented by using
    /// [ValueSize::value_size_sum_iter]. For [Sized] types, a usually more
    /// efficient implementation using [ExactSizeIterator::len] is provided. If
    /// you are implementing this trait manually, it is unlikely to be more
    /// efficient to provide a manual implementation here.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::ValueSize;
    ///
    /// let nums: [i32; 3] = [1, 2, 3];
    ///
    /// assert_eq!(12, i32::value_size_sum_exact_size_iter(nums.iter()));
    /// ```
    fn value_size_sum_exact_size_iter<'item>(iterator: impl ExactSizeIterator<Item = &'item Self>)
        -> usize
    where
        Self: 'item
    {
        Self::value_size_sum_iter(iterator)
    }
}

impl<T: Sized> ValueSize for T {
    fn value_size(&self) -> usize {
        mem::size_of::<Self>()
    }

    fn value_size_sum_iter<'item>(iterator: impl Iterator<Item = &'item Self>) -> usize
    where
        Self: 'item
    {
        mem::size_of::<Self>() * iterator.count()
    }

    fn value_size_sum_exact_size_iter<'item>(iterator: impl ExactSizeIterator<Item = &'item Self>)
        -> usize
    where
        Self: 'item
    {
        mem::size_of::<Self>() * iterator.len()
    }
}

/// A trait for types whose total size in memory can be determined at runtime.
/// This is required for the [LruCache](crate::LruCache) to track the size of
/// entries. It has implementations for most common data types and containers.
///
/// Note that reference-counting smart pointers deliberately do not implement
/// this trait, as it is not clear whether a pointer will drop the referenced
/// content when it is ejected from the cache.
///
/// This trait is blanked-implemented via the [HeapSize] and [ValueSize]
/// traits. For [Sized] types, it suffices to implement [HeapSize], otherwise
/// implement both [HeapSize] and [ValueSize]. This trait will be automatically
/// implemented.
pub trait MemSize : ValueSize + HeapSize {

    /// The total size of this value in bytes. This includes the value itself
    /// as well as all owned referenced data (such as the value on the heap of
    /// a [Box] or the elements and reserved memory of a [Vec]).
    ///
    /// This function is blanket-implemented by adding [ValueSize::value_size]
    /// and [HeapSize::heap_size] for any given value.
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::MemSize;
    /// use std::mem;
    ///
    /// assert_eq!(8, 1u64.mem_size());
    /// assert_eq!(12 + mem::size_of::<String>(),
    ///     "hello world!".to_owned().mem_size());
    /// ```
    fn mem_size(&self) -> usize;
}

impl<T: HeapSize + ValueSize + ?Sized> MemSize for T {
    fn mem_size(&self) -> usize {
        self.value_size() + self.heap_size()
    }
}

macro_rules! basic_mem_size {
    ( $t: ty ) => {
        impl HeapSize for $t {
            fn heap_size(&self) -> usize {
                0
            }

            fn heap_size_sum_iter<'item, Fun, Iter>(_make_iter: Fun) -> usize
            where
                Self: 'item,
                Fun: Fn() -> Iter,
                Iter: Iterator<Item = &'item Self>
            {
                0
            }

            fn heap_size_sum_exact_size_iter<'item, Fun, Iter>(_make_iter: Fun) -> usize
            where
                Self: 'item,
                Fun: Fn() -> Iter,
                Iter: ExactSizeIterator<Item = &'item Self>
            {
                0
            }
        }
    };
}

basic_mem_size!(());
basic_mem_size!(u8);
basic_mem_size!(u16);
basic_mem_size!(u32);
basic_mem_size!(u64);
basic_mem_size!(u128);
basic_mem_size!(usize);
basic_mem_size!(i8);
basic_mem_size!(i16);
basic_mem_size!(i32);
basic_mem_size!(i64);
basic_mem_size!(i128);
basic_mem_size!(isize);
basic_mem_size!(f32);
basic_mem_size!(f64);
basic_mem_size!(bool);
basic_mem_size!(char);

basic_mem_size!(str);
basic_mem_size!(CStr);
basic_mem_size!(OsStr);

basic_mem_size!(NonZeroU8);
basic_mem_size!(NonZeroU16);
basic_mem_size!(NonZeroU32);
basic_mem_size!(NonZeroU64);
basic_mem_size!(NonZeroU128);
basic_mem_size!(NonZeroUsize);
basic_mem_size!(NonZeroI8);
basic_mem_size!(NonZeroI16);
basic_mem_size!(NonZeroI32);
basic_mem_size!(NonZeroI64);
basic_mem_size!(NonZeroI128);
basic_mem_size!(NonZeroIsize);

basic_mem_size!(Ordering);

basic_mem_size!(Duration);
basic_mem_size!(Instant);

basic_mem_size!(Alignment);

basic_mem_size!(PhantomPinned);

basic_mem_size!(Shutdown);

basic_mem_size!(RangeFull);

basic_mem_size!(ThreadId);

basic_mem_size!(Ipv4Addr);
basic_mem_size!(Ipv6Addr);
basic_mem_size!(IpAddr);
basic_mem_size!(SocketAddrV4);
basic_mem_size!(SocketAddrV6);
basic_mem_size!(SocketAddr);

basic_mem_size!(RandomState);

macro_rules! tuple_mem_size {
    ( $($ts: ident),+ ) => {
        impl<$($ts),+> HeapSize for ($($ts,)+)
        where
            $($ts: HeapSize),+
        {
            fn heap_size(&self) -> usize {
                #[allow(non_snake_case)]
                let ($($ts,)+) = self;
                0 $(+ $ts.heap_size())+
            }

            // TODO specialized impls
        }
    };
}

tuple_mem_size!(A);
tuple_mem_size!(A, B);
tuple_mem_size!(A, B, C);
tuple_mem_size!(A, B, C, D);
tuple_mem_size!(A, B, C, D, E);
tuple_mem_size!(A, B, C, D, E, F);
tuple_mem_size!(A, B, C, D, E, F, G);
tuple_mem_size!(A, B, C, D, E, F, G, H);
tuple_mem_size!(A, B, C, D, E, F, G, H, I);
tuple_mem_size!(A, B, C, D, E, F, G, H, I, J);

impl<T: MemSize> HeapSize for Wrapping<T> {
    fn heap_size(&self) -> usize {
        self.0.heap_size()
    }

    fn heap_size_sum_iter<'item, Fun, Iter>(make_iter: Fun) -> usize
    where
        Self: 'item,
        Fun: Fn() -> Iter,
        Iter: Iterator<Item = &'item Self>
    {
        T::heap_size_sum_iter(|| make_iter().map(|item| &item.0))
    }

    fn heap_size_sum_exact_size_iter<'item, Fun, Iter>(make_iter: Fun) -> usize
    where
        Self: 'item,
        Fun: Fn() -> Iter,
        Iter: ExactSizeIterator<Item = &'item Self>
    {
        T::heap_size_sum_iter(|| make_iter().map(|item| &item.0))
    }
}

impl<T> ValueSize for [T] {
    fn value_size(&self) -> usize {
        mem::size_of_val(self)
    }
}

impl<T: MemSize> HeapSize for [T] {
    fn heap_size(&self) -> usize {
        T::heap_size_sum_exact_size_iter(|| self.iter())
    }
}

impl<T: MemSize, const N: usize> HeapSize for [T; N] {
    fn heap_size(&self) -> usize {
        self[..].heap_size()
    }

    fn heap_size_sum_iter<'item, Fun, Iter>(make_iter: Fun) -> usize
    where
        Self: 'item,
        Fun: Fn() -> Iter,
        Iter: Iterator<Item = &'item Self>
    {
        <[T]>::heap_size_sum_iter(|| make_iter().map(|item| &item[..]))
    }

    // TODO exact size iter
}

impl<T: MemSize> HeapSize for Vec<T> {
    fn heap_size(&self) -> usize {
        let element_heap_size = self.as_slice().heap_size();
        let own_heap_size = self.capacity() * mem::size_of::<T>();
        element_heap_size + own_heap_size
    }
}

impl<K: MemSize, V: MemSize, S: MemSize> HeapSize for HashMap<K, V, S> {
    fn heap_size(&self) -> usize {
        let hasher_heap_size = self.hasher().heap_size();
        // TODO use specialized impls
        let element_heap_size = self.iter()
            .map(|(k, v)| k.heap_size() + v.heap_size())
            .sum::<usize>();
        let key_value_size = mem::size_of::<(K, V)>();
        let own_heap_size = self.capacity() * key_value_size;

        hasher_heap_size + element_heap_size + own_heap_size
    }
}

impl<T: MemSize, S: MemSize> HeapSize for HashSet<T, S> {
    fn heap_size(&self) -> usize {
        let hasher_heap_size = self.hasher().heap_size();
        let element_heap_size = T::heap_size_sum_exact_size_iter(|| self.iter());
        let own_heap_size = self.capacity() * mem::size_of::<T>();

        hasher_heap_size + element_heap_size + own_heap_size
    }
}

impl<T: MemSize> HeapSize for BinaryHeap<T> {
    fn heap_size(&self) -> usize {
        let element_heap_size = T::heap_size_sum_exact_size_iter(|| self.iter());
        let own_heap_size = self.capacity() * mem::size_of::<T>();

        element_heap_size + own_heap_size
    }
}

impl<T: MemSize + ?Sized> HeapSize for Box<T> {
    fn heap_size(&self) -> usize {
        T::mem_size(self.as_ref())
    }

    fn heap_size_sum_iter<'item, Fun, Iter>(make_iter: Fun) -> usize
    where
        Self: 'item,
        Fun: Fn() -> Iter,
        Iter: Iterator<Item = &'item Self>
    {
        T::heap_size_sum_iter(|| make_iter().map(|item| &**item)) +
            T::value_size_sum_iter(make_iter().map(|item| &**item))
    }

    fn heap_size_sum_exact_size_iter<'item, Fun, Iter>(make_iter: Fun) -> usize
    where
        Self: 'item,
        Fun: Fn() -> Iter,
        Iter: ExactSizeIterator<Item = &'item Self>
    {
        T::heap_size_sum_exact_size_iter(|| make_iter().map(|item| &**item)) +
            T::value_size_sum_exact_size_iter(make_iter().map(|item| &**item))
    }
}

impl<T: MemSize> HeapSize for Mutex<T> {
    fn heap_size(&self) -> usize {
        self.lock().unwrap().heap_size()
    }
}

impl<T: MemSize> HeapSize for RwLock<T> {
    fn heap_size(&self) -> usize {
        self.read().unwrap().heap_size()
    }
}

impl ValueSize for str {
    fn value_size(&self) -> usize {
        mem::size_of_val(self)
    }
}

impl HeapSize for String {
    fn heap_size(&self) -> usize {
        self.capacity()
    }
}

impl ValueSize for CStr {
    fn value_size(&self) -> usize {
        mem::size_of_val(self)
    }
}

impl HeapSize for CString {
    fn heap_size(&self) -> usize {
        self.as_bytes_with_nul().len()
    }
}

impl ValueSize for OsStr {
    fn value_size(&self) -> usize {
        mem::size_of_val(self)
    }
}

impl HeapSize for OsString {
    fn heap_size(&self) -> usize {
        self.capacity()
    }
}

impl<T: ?Sized> HeapSize for &T {
    fn heap_size(&self) -> usize {
        // cache is not data owner => only memory for reference itself counted
        0
    }
}

impl<T: ?Sized> HeapSize for &mut T {
    fn heap_size(&self) -> usize {
        // cache is not data owner => only memory for reference itself counted
        0
    }
}

impl<T: MemSize> HeapSize for Option<T> {
    fn heap_size(&self) -> usize {
        match self {
            Some(v) => v.heap_size(),
            None => 0
        }
    }
}

impl<V: MemSize, E: MemSize> HeapSize for Result<V, E> {
    fn heap_size(&self) -> usize {
        match self {
            Ok(v) => v.heap_size(),
            Err(e) => e.heap_size()
        }
    }
}

impl<T> HeapSize for PhantomData<T> {
    fn heap_size(&self) -> usize {
        0
    }
}

impl<I: MemSize> HeapSize for Range<I> {
    fn heap_size(&self) -> usize {
        self.start.heap_size() + self.end.heap_size()
    }
}

impl<I: MemSize> HeapSize for RangeFrom<I> {
    fn heap_size(&self) -> usize {
        self.start.heap_size()
    }
}

impl<I: MemSize> HeapSize for RangeTo<I> {
    fn heap_size(&self) -> usize {
        self.end.heap_size()
    }
}

impl<I: MemSize> HeapSize for RangeInclusive<I> {
    fn heap_size(&self) -> usize {
        self.start().heap_size() + self.end().heap_size()
    }
}

impl<I: MemSize> HeapSize for RangeToInclusive<I> {
    fn heap_size(&self) -> usize {
        self.end.heap_size()
    }
}

impl HeapSize for Path {
    fn heap_size(&self) -> usize {
        0
    }
}

impl ValueSize for Path {
    fn value_size(&self) -> usize {
        mem::size_of_val(self)
    }
}

impl HeapSize for PathBuf {
    fn heap_size(&self) -> usize {
        self.as_path().mem_size()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    const VEC_SIZE: usize = mem::size_of::<Vec<u8>>();
    const STRING_SIZE: usize = mem::size_of::<String>();
    const BOXED_SLICE_SIZE: usize = mem::size_of::<Box<[u8]>>();
    const HASH_MAP_SIZE: usize = mem::size_of::<HashMap<u8, u8>>();
    const HASH_SET_SIZE: usize = mem::size_of::<HashSet<u8>>();
    const BINARY_HEAP_SIZE: usize = mem::size_of::<BinaryHeap<u8>>();
    const STRING_RESULT_SIZE: usize = mem::size_of::<Result<String, String>>();
    const PATH_BUF_SIZE: usize = mem::size_of::<PathBuf>();

    #[test]
    fn tuples_have_correct_size() {
        assert_eq!(mem::size_of::<(u16, u32, i16, char)>(),
            (1u16, 2u32, 3i16, 'x').mem_size());
        assert_eq!(mem::size_of::<((u8, i8, u8), i16)>(),
            ((1u8, 2i8, 3u8), 4i16).mem_size());
    }

    #[test]
    fn vectors_have_correct_size() {
        assert_eq!(24 + VEC_SIZE,
            vec!['a', 'b', 'c', 'd', 'e', 'f'].mem_size());
        assert_eq!(24 + 4 * VEC_SIZE,
            vec![vec![], vec![1u64, 2u64], vec![3u64]].mem_size());
    }

    #[test]
    fn vectors_estimate_spare_capacity() {
        let mut vec = Vec::with_capacity(8);

        assert_eq!(64 + VEC_SIZE, vec.mem_size());

        vec.push(1.0f64);

        assert_eq!(64 + VEC_SIZE, vec.mem_size());
    }

    #[test]
    fn byte_vector_has_correct_size() {
        assert_eq!(5 + VEC_SIZE, vec![0u8; 5].mem_size());
    }

    #[test]
    fn boxed_byte_vector_has_correct_size() {
        let box_size = mem::size_of::<Box<u8>>();
        let vec = vec![Box::new(0u8); 5];
        let expected_size = 5 + 5 * box_size + VEC_SIZE;

        assert_eq!(expected_size, vec.mem_size());
    }

    #[test]
    fn string_vector_has_correct_size() {
        let vec = vec![
            "hello".to_owned(),
            "world".to_owned(),
            "greetings".to_owned(),
            "moon".to_owned()
        ];
        let expected_size = 23 + 4 * STRING_SIZE + VEC_SIZE;

        assert_eq!(expected_size, vec.mem_size());
    }

    #[test]
    fn strings_have_correct_size() {
        assert_eq!(11 + STRING_SIZE, "hello world".to_owned().mem_size());
        assert_eq!(26 + STRING_SIZE,
            "söme döüble byte chärs".to_owned().mem_size());
    }

    #[test]
    fn string_with_spare_capacity_has_correct_size() {
        assert_eq!(16 + STRING_SIZE, String::with_capacity(16).mem_size());
    }

    #[test]
    fn options_have_correct_size() {
        let some = Some(String::from("hello"));
        let none = None::<String>;

        assert_eq!(none.mem_size() + 5, some.mem_size());
    }

    #[test]
    fn wrapping_have_correct_size() {
        let wrapping = Wrapping(0u64);

        assert_eq!(8, wrapping.mem_size());
    }

    #[test]
    fn arrays_with_primitive_entries_have_correct_size() {
        let array = [0u64; 4];

        assert_eq!(32, array.mem_size());
    }

    #[test]
    fn arrays_with_complex_entries_have_correct_size() {
        let array = [vec![], Vec::<u64>::with_capacity(4)];

        assert_eq!(2 * VEC_SIZE + 32, array.mem_size());
    }

    #[test]
    fn boxed_slices_with_primitive_entries_have_correct_size() {
        let slice = vec![1u32, 2u32, 3u32, 4u32].into_boxed_slice();

        assert_eq!(BOXED_SLICE_SIZE + 16, Box::mem_size(&slice));
    }

    #[test]
    fn boxed_slices_with_complex_entries_have_correct_size() {
        let slice =
            vec![vec![], Vec::<u64>::with_capacity(4)].into_boxed_slice();

        assert_eq!(BOXED_SLICE_SIZE + 2 * VEC_SIZE + 32, Box::mem_size(&slice));
    }

    #[test]
    fn empty_hash_map_has_correct_size() {
        let hash_map = HashMap::<String, String>::new();

        assert_eq!(HASH_MAP_SIZE, hash_map.mem_size());
    }

    #[test]
    fn hash_map_of_primitives_with_abnormal_alignment_has_correct_size() {
        const ENTRY_SIZE: usize = mem::size_of::<(u8, u16)>();

        let mut hash_map = HashMap::new();
        hash_map.insert(0u8, 1u16);
        hash_map.insert(1u8, 2u16);
        hash_map.insert(2u8, 3u16);

        let expected_size = ENTRY_SIZE * hash_map.capacity() + HASH_MAP_SIZE;

        assert_eq!(expected_size, hash_map.mem_size());
    }

    #[test]
    fn hash_map_of_complex_entries_has_correct_size() {
        const ENTRY_SIZE: usize = mem::size_of::<(String, String)>();

        let mut hash_map = HashMap::new();
        hash_map.insert("hello".to_owned(), "world".to_owned());
        hash_map.insert("greetings".to_owned(), "moon".to_owned());
        hash_map.insert("ahoy".to_owned(), "mars".to_owned());

        let number_of_chars = 31;
        let expected_size =
            ENTRY_SIZE * hash_map.capacity() + HASH_MAP_SIZE + number_of_chars;

        assert_eq!(expected_size, hash_map.mem_size());
    }

    #[test]
    fn empty_hash_set_has_correct_size() {
        let hash_set = HashSet::<String>::new();

        assert_eq!(HASH_SET_SIZE, hash_set.mem_size());
    }

    #[test]
    fn hash_set_of_primitives_has_correct_size() {
        let mut hash_set = HashSet::new();
        hash_set.insert(1u16);
        hash_set.insert(2u16);
        hash_set.insert(3u16);

        let expected_size = 2 * hash_set.capacity() + HASH_SET_SIZE;

        assert_eq!(expected_size, hash_set.mem_size());
    }

    #[test]
    fn hash_set_of_complex_entries_has_correct_size() {
        let mut hash_set = HashSet::new();
        hash_set.insert("hello".to_owned());
        hash_set.insert("greetings".to_owned());
        hash_set.insert("ahoy".to_owned());

        let number_of_chars = 18;
        let expected_size =
            STRING_SIZE * hash_set.capacity() + HASH_SET_SIZE + number_of_chars;

        assert_eq!(expected_size, hash_set.mem_size());
    }

    #[test]
    fn empty_binary_heap_has_correct_size() {
        let binary_heap = BinaryHeap::<String>::new();

        assert_eq!(BINARY_HEAP_SIZE, binary_heap.mem_size());
    }

    #[test]
    fn binary_heap_of_primitives_has_correct_size() {
        let mut binary_heap = BinaryHeap::with_capacity(5);
        binary_heap.push(1u16);
        binary_heap.push(2u16);
        binary_heap.push(3u16);

        assert_eq!(BINARY_HEAP_SIZE + 10, binary_heap.mem_size());
    }

    #[test]
    fn binary_heap_of_complex_entries_has_correct_size() {
        let mut binary_heap = BinaryHeap::with_capacity(7);
        binary_heap.push("hello".to_owned());
        binary_heap.push("greetings".to_owned());
        binary_heap.push("ahoy".to_owned());

        let number_of_chars = 18;
        let expected_size =
            STRING_SIZE * 7 + BINARY_HEAP_SIZE + number_of_chars;

        assert_eq!(expected_size, binary_heap.mem_size());
    }

    #[test]
    fn mutex_of_primitive_type_has_correct_size() {
        let mutex = Mutex::new(0u64);

        assert_eq!(mem::size_of::<Mutex<u64>>(), mutex.mem_size());
    }

    #[test]
    fn mutex_of_complex_type_has_correct_size() {
        let mutex = Mutex::new("hello".to_owned());

        assert_eq!(mem::size_of::<Mutex<String>>() + 5, mutex.mem_size());
    }

    #[test]
    fn rw_lock_of_primitive_type_has_correct_size() {
        let rw_lock = RwLock::new(0u64);

        assert_eq!(mem::size_of::<RwLock<u64>>(), rw_lock.mem_size());
    }

    #[test]
    fn rw_lock_of_complex_type_has_correct_size() {
        let rw_lock = RwLock::new("hello".to_owned());

        assert_eq!(mem::size_of::<RwLock<String>>() + 5, rw_lock.mem_size());
    }

    #[test]
    fn boxed_str_has_correct_size() {
        let string = "hello".to_owned().into_boxed_str();

        assert_eq!(mem::size_of::<Box<str>>() + 5, string.mem_size());
    }

    #[test]
    fn boxed_cstr_has_correct_size() {
        let string = CString::new("hello").unwrap().into_boxed_c_str();

        assert_eq!(mem::size_of::<Box<CStr>>() + 6, string.mem_size());
    }

    #[test]
    fn cstring_has_correct_size(){
        let string = CString::new("hello").unwrap();

        assert_eq!(mem::size_of::<CString>() + 6, string.mem_size());
    }

    #[test]
    fn references_have_correct_size() {
        assert_eq!(mem::size_of::<&u8>(),
            <&String>::mem_size(&&"hello".to_owned()));
        assert_eq!(mem::size_of::<&u8>(),
            <&mut String>::mem_size(&&mut "hello".to_owned()));
    }

    #[test]
    fn some_variant_of_primitive_type_has_correct_size() {
        assert_eq!(2, Some(NonZeroI16::new(1).unwrap()).mem_size());
    }

    #[test]
    fn some_variant_of_complex_type_has_correct_size() {
        let option = Some("hello".to_owned()).mem_size();

        assert_eq!(mem::size_of::<Option<String>>() + 5, option);
    }

    #[test]
    fn none_variant_has_correct_size() {
        assert_eq!(2, None::<NonZeroI16>.mem_size());
    }

    #[test]
    fn ok_variant_of_primitive_type_has_correct_size() {
        let result: Result<u64, u64> = Ok(1);

        assert_eq!(mem::size_of::<Result<u64, u64>>(), result.mem_size());
    }

    #[test]
    fn err_variant_of_primitive_type_has_correct_size() {
        let result: Result<u32, u32> = Err(2);

        assert_eq!(mem::size_of::<Result<u32, u32>>(), result.mem_size());
    }

    #[test]
    fn ok_variant_of_complex_type_has_correct_size() {
        let result: Result<String, String> = Ok("hello".to_owned());

        assert_eq!(STRING_RESULT_SIZE + 5, result.mem_size());
    }

    #[test]
    fn err_variant_of_complex_type_has_correct_size() {
        let result: Result<String, String> = Err("world".to_owned());

        assert_eq!(STRING_RESULT_SIZE + 5, result.mem_size());
    }

    #[test]
    fn phantom_data_has_zero_size() {
        assert_eq!(0, PhantomData::<String>.mem_size());
    }

    #[test]
    fn ip_addresses_have_correct_size() {
        const IP_ADDR_SIZE: usize = mem::size_of::<IpAddr>();

        let v4 = IpAddr::V4("1.2.3.4".parse().unwrap());
        let v6 = IpAddr::V6("1234::4321".parse().unwrap());

        assert_eq!(IP_ADDR_SIZE, v4.mem_size());
        assert_eq!(IP_ADDR_SIZE, v6.mem_size());
    }

    #[test]
    fn socket_addresses_have_correct_size() {
        const SOCKET_ADDR_SIZE: usize = mem::size_of::<SocketAddr>();

        let v4 = SocketAddr::V4("1.2.3.4:1337".parse().unwrap());
        let v6 = SocketAddr::V6("[1234::4321]:1337".parse().unwrap());

        assert_eq!(SOCKET_ADDR_SIZE, v4.mem_size());
        assert_eq!(SOCKET_ADDR_SIZE, v6.mem_size());
    }

    #[test]
    fn full_range_has_zero_size() {
        assert_eq!(0, (..).mem_size());
    }

    struct MockRangeable {
        heap_size: usize
    }

    impl MockRangeable {
        fn new(heap_size: usize) -> MockRangeable {
            MockRangeable { heap_size }
        }
    }

    impl HeapSize for MockRangeable {
        fn heap_size(&self) -> usize {
            self.heap_size
        }
    }

    #[test]
    fn ranges_have_correct_size() {
        let range_from = MockRangeable::new(42)..;
        let range_to = ..MockRangeable::new(42);
        let range_to_inclusive = ..=MockRangeable::new(42);
        let range = MockRangeable::new(42)..MockRangeable::new(43);
        let range_inclusive = MockRangeable::new(42)..=MockRangeable::new(43);

        assert_eq!(mem::size_of::<RangeFrom<MockRangeable>>() + 42,
            range_from.mem_size());
        assert_eq!(mem::size_of::<RangeTo<MockRangeable>>() + 42,
            range_to.mem_size());
        assert_eq!(mem::size_of::<RangeToInclusive<MockRangeable>>() + 42,
            range_to_inclusive.mem_size());
        assert_eq!(mem::size_of::<Range<MockRangeable>>() + 85,
            range.mem_size());
        assert_eq!(mem::size_of::<RangeInclusive<MockRangeable>>() + 85,
            range_inclusive.mem_size());
    }

    #[test]
    fn empty_path_has_correct_size() {
        let path = Path::new("");

        assert_eq!(0, path.mem_size());
    }

    #[test]
    fn non_empty_path_has_correct_size() {
        let path = Path::new("hello");
        let os_str = OsStr::new("hello");

        assert_eq!(os_str.mem_size(), path.mem_size());
    }

    #[test]
    fn empty_path_buf_has_correct_size() {
        let path_buf = PathBuf::new();

        assert_eq!(PATH_BUF_SIZE, path_buf.mem_size());
    }

    #[test]
    fn non_empty_path_buf_has_correct_size() {
        let path_buf = PathBuf::from("hello/world");
        let os_str = OsStr::new("hello/world");

        assert_eq!(PATH_BUF_SIZE + os_str.mem_size(), path_buf.mem_size());
    }
}
