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
/// blanket implementation of [MemSize] is alread provided. The latter is
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

    /// The size of the referenced data that is owned by this value, usually
    /// allocated on the heap (such as the value of a [Box] or the elements and
    /// reserved memory of a [Vec]).
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
}

/// A trait for types whose total size in memory can be determined at runtime.
/// This is required for the [LruCache](crate::LruCache) to track the size of
/// entries. It has implementations for most common data types and containers.
///
/// Note that reference-counting smart pointers deliberately do not implement
/// this trait, as it is not clear whether a pointer will drop the referenced
/// content when it is ejected from the cache.
///
/// # Example
///
/// For [Sized] types, you do not need to implement this trait. Instead,
/// implement [HeapSize].
///
/// Should your type not be [Sized], you need to account for both heap and
/// value data. Consider as an example the implementation of [HeapSize] and
/// `MemSize` on `[T]` for any type `T` that implements `MemSize`.
///
/// ```ignore
/// use lru_mem::{HeapSize, MemSize};
/// use std::mem;
///
/// impl<T: MemSize> HeapSize for [T] {
///     fn heap_size(&self) -> usize {
///         // Take the sum of the heap sizes of all elements in this array.
///         self.iter().map(|t| t.heap_size()).sum()
///     }
/// }
/// 
/// impl<T: MemSize> MemSize for [T] {
///     fn mem_size(&self) -> usize {
///         // Take the total heap size of this array AND the memory allocated
///         // for the element values itself.
///         self.heap_size() + mem::size_of::<T>() * self.len()
///     }
/// }
/// ```
pub trait MemSize : HeapSize {

    /// The total size of this value in bytes. This includes the value itself
    /// as well as all owned referenced data (such as the value on the heap of
    /// a [Box] or the elements and reserved memory of a [Vec]).
    ///
    /// For [Sized] types, this is always implemented as adding [mem::size_of]
    /// of `Self` to [HeapSize::heap_size]. Non-[Sized] types must provide a
    /// custom implementation.
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

impl<T: Sized + HeapSize> MemSize for T {
    fn mem_size(&self) -> usize {
        mem::size_of::<T>() + self.heap_size()
    }
}

macro_rules! basic_mem_size {
    ( $t: ty ) => {
        impl HeapSize for $t {
            fn heap_size(&self) -> usize {
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
basic_mem_size!(SocketAddrV4);
basic_mem_size!(SocketAddrV6);

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
}

fn sum_heap_size<'a, T, I>(iter: I) -> usize
where
    T: MemSize + 'a,
    I: IntoIterator<Item = &'a T>
{
    iter.into_iter().map(|t| t.heap_size()).sum()
}

impl<T: MemSize> HeapSize for [T] {
    fn heap_size(&self) -> usize {
        sum_heap_size(self)
    }
}

impl<T: MemSize> MemSize for [T] {
    fn mem_size(&self) -> usize {
        self.heap_size() + mem::size_of::<T>() * self.len()
    }
}

impl<T: MemSize, const N: usize> HeapSize for [T; N] {
    fn heap_size(&self) -> usize {
        (&self[..]).heap_size()
    }
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
        let element_heap_size = self.iter()
            .map(|(k, v)| k.heap_size() + v.heap_size())
            .sum::<usize>();
        let key_value_size = mem::size_of::<K>() + mem::size_of::<V>();
        let own_heap_size = self.capacity() * key_value_size;

        hasher_heap_size + element_heap_size + own_heap_size
    }
}

impl<T: MemSize, S: MemSize> HeapSize for HashSet<T, S> {
    fn heap_size(&self) -> usize {
        let hasher_heap_size = self.hasher().heap_size();
        let element_heap_size = sum_heap_size(self);
        let own_heap_size = self.capacity() * mem::size_of::<T>();

        hasher_heap_size + element_heap_size + own_heap_size
    }
}

impl<T: MemSize> HeapSize for BinaryHeap<T> {
    fn heap_size(&self) -> usize {
        let element_heap_size = sum_heap_size(self.iter());
        let own_heap_size = self.capacity() * mem::size_of::<T>();

        element_heap_size + own_heap_size
    }
}

impl<T: MemSize> HeapSize for Box<T> {
    fn heap_size(&self) -> usize {
        self.as_ref().mem_size()
    }
}

impl<T: MemSize> HeapSize for Mutex<T> {
    fn heap_size(&self) -> usize {
        self.lock().unwrap().mem_size()
    }
}

impl<T: MemSize> HeapSize for RwLock<T> {
    fn heap_size(&self) -> usize {
        self.read().unwrap().mem_size()
    }
}

impl HeapSize for str {
    fn heap_size(&self) -> usize {
        0
    }
}

impl MemSize for str {
    fn mem_size(&self) -> usize {
        self.len()
    }
}

impl HeapSize for String {
    fn heap_size(&self) -> usize {
        self.capacity()
    }
}

impl HeapSize for CStr {
    fn heap_size(&self) -> usize {
        0
    }
}

impl MemSize for CStr {
    fn mem_size(&self) -> usize {
        self.to_bytes_with_nul().len()
    }
}

impl HeapSize for CString {
    fn heap_size(&self) -> usize {
        self.as_bytes_with_nul().len()
    }
}

impl HeapSize for OsStr {
    fn heap_size(&self) -> usize {
        0
    }
}

impl MemSize for OsStr {
    fn mem_size(&self) -> usize {
        self.len()
    }
}

impl HeapSize for OsString {
    fn heap_size(&self) -> usize {
        self.capacity()
    }
}

impl<T: ?Sized> HeapSize for &T {
    fn heap_size(&self) -> usize {
        0
    }
}

impl<T: ?Sized> HeapSize for &mut T {
    fn heap_size(&self) -> usize {
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

impl HeapSize for IpAddr {
    fn heap_size(&self) -> usize {
        match self {
            IpAddr::V4(v4) => v4.heap_size(),
            IpAddr::V6(v6) => v6.heap_size()
        }
    }
}

impl HeapSize for SocketAddr {
    fn heap_size(&self) -> usize {
        match self {
            SocketAddr::V4(v4) => v4.heap_size(),
            SocketAddr::V6(v6) => v6.heap_size()
        }
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

impl MemSize for Path {
    fn mem_size(&self) -> usize {
        self.as_os_str().mem_size()
    }
}

impl HeapSize for PathBuf {
    fn heap_size(&self) -> usize {
        self.as_path().mem_size()
    }
}
