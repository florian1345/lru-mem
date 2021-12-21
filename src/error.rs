use std::error::Error;
use std::fmt::{self, Debug, Display, Formatter};

/// An enumeration of the different errors that can occur while handling the
/// [LruCache](crate::LruCache).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LruError<K, V> {

    /// This error is raised if the amount of memory required to store an entry
    /// to be inserted, or after its modification, is larger than the maximum
    /// of the cache.
    EntryTooLarge {

        /// The key of the entry which was too large.
        key: K,

        /// The value of the entry which was too large.
        value: V,

        /// The computed size requirement of the entry if it were in the cache
        /// in bytes.
        entry_size: usize,

        /// The maximum size of the cache in bytes.
        max_size: usize
    }
}

impl<K, V> Display for LruError<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            LruError::EntryTooLarge { .. } =>
                write!(f, "entry does not fit in cache")
        }
    }
}

impl<K: Debug, V: Debug> Error for LruError<K, V> { }

/// Syntactic sugar for `Result<T, LruError<K, V>>`.
pub type LruResult<T, K, V> = Result<T, LruError<K, V>>;
