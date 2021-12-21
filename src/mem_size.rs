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
/// For simple types which are stored completely in one memory location, such
/// as primitive types or structs of such types, it usually suffices to
/// implement this as a call to [mem::size_of]. The example below illustrates
/// this.
///
/// ```
/// use lru_mem::MemSize;
/// use std::mem;
///
/// struct Vector2f {
///     x: f32,
///     y: f32
/// }
///
/// impl MemSize for Vector2f {
///     fn mem_size(&self) -> usize {
///         // Vector2f consists of two floats, which are stored as one value,
///         // so there is no additional heap memory allocated for a Vector2f.
///         // It therefore suffices to call mem::size_of.
///         mem::size_of::<Vector2f>()
///     }
/// }
/// ```
///
/// For more complicated types, it may be necessary to account for any
/// referenced data that is owned by the instance. If the memory is owned by
/// some field, which already implements `MemSize`, you can rely on that
/// implementation to estimate the required heap memory. See below for an
/// example of this.
///
/// ```
/// use lru_mem::MemSize;
///
/// struct Person {
///     name: String,
///     address: String
/// }
///
/// impl MemSize for Person {
///     fn mem_size(&self) -> usize {
///         // Both members may have allocated data, which is accounted for by
///         // calling mem_size. Note that strange alignment inside the Person
///         // struct may actually increase the memory requirement beyond the
///         // one computed here, but we assume it to be compact.
///         self.name.mem_size() + self.address.mem_size()
///     }
/// }
/// ```
///
/// In case the previous examples do not apply, consider the implementation on
/// [String] provided by this library. It demonstrates how to manually account
/// for any owned referenced data.
///
/// ```ignore
/// use lru_mem::MemSize;
/// use std::mem;
///
/// impl MemSize for String {
///     fn mem_size(&self) -> usize {
///         // The number of bytes reserved on the heap for UTF-8 data.
///         let heap_size = self.capacity();
///
///         // The number of bytes occupied by the value itself (on the stack
///         // or in whatever data structure).
///         let value_size = mem::size_of::<String>();
///         heap_size + value_size
///     }
/// }
/// ```
pub trait MemSize {

    /// The total size of this value in bytes. This includes the value itself
    /// as well as all owned referenced data (such as the value on the heap of
    /// a [Box] or the elements of a [Vec]).
    ///
    /// # Example
    ///
    /// ```
    /// use lru_mem::MemSize;
    /// use std::mem;
    ///
    /// assert_eq!(8, 1u64.mem_size());
    /// assert_eq!(12 + 3 * mem::size_of::<usize>(),
    ///     "hello world!".to_owned().mem_size());
    /// ```
    fn mem_size(&self) -> usize;
}

macro_rules! basic_mem_size {
    ( $t: ty ) => {
        impl MemSize for $t {
            fn mem_size(&self) -> usize {
                mem::size_of::<$t>()
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
        impl<$($ts),+> MemSize for ($($ts,)+)
        where
            $($ts: MemSize),+
        {
            fn mem_size(&self) -> usize {
                #[allow(non_snake_case)]
                let ($($ts,)+) = self;
                0 $(+ $ts.mem_size())+
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

impl<T> MemSize for Wrapping<T> {
    fn mem_size(&self) -> usize {
        mem::size_of::<Wrapping<T>>()
    }
}

fn sum_size<'a, T: MemSize + 'a>(iter: impl Iterator<Item = &'a T>) -> usize {
    iter.map(|t| t.mem_size()).sum()
}

impl<T: MemSize> MemSize for [T] {
    fn mem_size(&self) -> usize {
        sum_size(self.iter())
    }
}

impl<T: MemSize, const N: usize> MemSize for [T; N] {
    fn mem_size(&self) -> usize {
        (&self[..]).mem_size()
    }
}

impl<T: MemSize> MemSize for Vec<T> {
    fn mem_size(&self) -> usize {
        let element_size = self.as_slice().mem_size();
        let excess_size = (self.capacity() - self.len()) * mem::size_of::<T>();
        let value_size = mem::size_of::<Vec<T>>();

        element_size + excess_size + value_size
    }
}

impl<K: MemSize, V: MemSize, S: MemSize> MemSize for HashMap<K, V, S> {
    fn mem_size(&self) -> usize {
        let hasher_heap_size = self.hasher().mem_size() - mem::size_of::<S>();
        let element_size = self.iter()
            .map(|(k, v)| k.mem_size() + v.mem_size())
            .sum::<usize>();
        let entry_value_size = mem::size_of::<K>() + mem::size_of::<V>();
        let excess_size = (self.capacity() - self.len()) * entry_value_size;
        let value_size = mem::size_of::<HashMap<K, V, S>>();

        element_size + excess_size + value_size + hasher_heap_size
    }
}

impl<T: MemSize, S: MemSize> MemSize for HashSet<T, S> {
    fn mem_size(&self) -> usize {
        let hasher_heap_size = self.hasher().mem_size() - mem::size_of::<S>();
        let element_size = sum_size(self.iter());
        let excess_size = (self.capacity() - self.len()) * mem::size_of::<T>();
        let value_size = mem::size_of::<HashSet<T, S>>();

        element_size + excess_size + value_size + hasher_heap_size
    }
}

impl<T: MemSize> MemSize for BinaryHeap<T> {
    fn mem_size(&self) -> usize {
        let element_size = sum_size(self.iter());
        let excess_size = (self.capacity() - self.len()) * mem::size_of::<T>();
        let value_size = mem::size_of::<Vec<T>>();

        element_size + excess_size + value_size
    }
}

impl<T: MemSize> MemSize for Box<T> {
    fn mem_size(&self) -> usize {
        let heap_size = self.as_ref().mem_size();
        let value_size = mem::size_of::<Box<T>>();

        heap_size + value_size
    }
}

impl<T: MemSize> MemSize for Mutex<T> {
    fn mem_size(&self) -> usize {
        let heap_size = self.lock().unwrap().mem_size();
        let self_size = mem::size_of::<Mutex<T>>();

        heap_size + self_size
    }
}

impl<T: MemSize> MemSize for RwLock<T> {
    fn mem_size(&self) -> usize {
        let heap_size = self.read().unwrap().mem_size();
        let self_size = mem::size_of::<RwLock<T>>();

        heap_size + self_size
    }
}

impl MemSize for str {
    fn mem_size(&self) -> usize {
        self.len()
    }
}

impl MemSize for String {
    fn mem_size(&self) -> usize {
        self.capacity() + mem::size_of::<String>()
    }
}

impl MemSize for CStr {
    fn mem_size(&self) -> usize {
        self.to_bytes_with_nul().len()
    }
}

impl MemSize for CString {
    fn mem_size(&self) -> usize {
        self.as_bytes_with_nul().len() + mem::size_of::<CString>()
    }
}

impl MemSize for OsStr {
    fn mem_size(&self) -> usize {
        self.len()
    }
}

impl MemSize for OsString {
    fn mem_size(&self) -> usize {
        self.capacity() + mem::size_of::<OsString>()
    }
}

impl<T: ?Sized> MemSize for &T {
    fn mem_size(&self) -> usize {
        mem::size_of::<&T>()
    }
}

impl<T: ?Sized> MemSize for &mut T {
    fn mem_size(&self) -> usize {
        mem::size_of::<&mut T>()
    }
}

impl<T: MemSize> MemSize for Option<T> {
    fn mem_size(&self) -> usize {
        let value_size = mem::size_of::<Option<T>>();

        match self {
            Some(v) => v.mem_size() - mem::size_of::<T>() + value_size,
            None => value_size
        }
    }
}

impl<V: MemSize, E: MemSize> MemSize for Result<V, E> {
    fn mem_size(&self) -> usize {
        let value_size = mem::size_of::<Result<V, E>>();

        match self {
            Ok(v) => v.mem_size() - mem::size_of::<V>() + value_size,
            Err(e) => e.mem_size() - mem::size_of::<E>() + value_size
        }
    }
}

impl<T> MemSize for PhantomData<T> {
    fn mem_size(&self) -> usize {
        0
    }
}

impl MemSize for IpAddr {
    fn mem_size(&self) -> usize {
        let value_size = mem::size_of::<IpAddr>();

        match self {
            IpAddr::V4(v4) =>
                v4.mem_size() - mem::size_of::<Ipv4Addr>() + value_size,
            IpAddr::V6(v6) =>
                v6.mem_size() - mem::size_of::<Ipv6Addr>() + value_size
        }
    }
}

impl MemSize for SocketAddr {
    fn mem_size(&self) -> usize {
        let value_size = mem::size_of::<SocketAddr>();

        match self {
            SocketAddr::V4(v4) =>
                v4.mem_size() - mem::size_of::<SocketAddrV4>() + value_size,
            SocketAddr::V6(v6) =>
                v6.mem_size() - mem::size_of::<SocketAddrV6>() + value_size
        }
    }
}

impl<I: MemSize> MemSize for Range<I> {
    fn mem_size(&self) -> usize {
        self.start.mem_size() + self.end.mem_size()
    }
}

impl<I: MemSize> MemSize for RangeFrom<I> {
    fn mem_size(&self) -> usize {
        self.start.mem_size()
    }
}

impl<I: MemSize> MemSize for RangeTo<I> {
    fn mem_size(&self) -> usize {
        self.end.mem_size()
    }
}

impl<I: MemSize> MemSize for RangeInclusive<I> {
    fn mem_size(&self) -> usize {
        self.start().mem_size() + self.end().mem_size()
    }
}

impl<I: MemSize> MemSize for RangeToInclusive<I> {
    fn mem_size(&self) -> usize {
        self.end.mem_size()
    }
}

impl MemSize for Path {
    fn mem_size(&self) -> usize {
        self.as_os_str().mem_size()
    }
}

impl MemSize for PathBuf {
    fn mem_size(&self) -> usize {
        self.capacity() + mem::size_of::<PathBuf>()
    }
}
