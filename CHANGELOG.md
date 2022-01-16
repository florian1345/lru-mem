# v0.2

## v0.2.0

* Introduced new API for `LruCache` to better match `HashMap`
    * `try_insert`
    * `retain`
    * `get_entry`/`peek_entry` to match `HashMap`'s `get_key_value`
    * `into_keys`/`into_values`
    * `hasher`
* Introduced new `HeapSize` trait that determines the size of referenced data
    * Useful for easier `MemSize` implementation of collections
    * `MemSize` is blanket-implemented for `HeapSize + Sized`
* Introduced new error types -- one for each fallible situation
    * `InsertError` for fails in `LruCache::insert`
    * `TryInsertError` for fails in `LruCache::try_insert`
    * `MutateError` for fails in `LruCache::mutate`
    * Removed `LruError`
* Some minor documentation improvements
* Internal restructuring which may change the performance in some situations

# v0.1

## v0.1.5

* Allowed `mutate` to take an `FnOnce` instead of an `Fn`
* Implemented `Debug` for `LruCache` when `K` and `V` also implement `Debug`
* Significant restructuring with performance improvements for most methods

## v0.1.4

* Exposed an `entry_size` method to compute the requirement of entries
* Fixed `reserve` and `try_reserve` not handling errors correctly
* Improved documentation

## v0.1.3

* Implemented `Send` and `Sync` for `LruCache`
* Minor performance improvement for cloning and reallocating
* Fixed typo in documentation

## v0.1.2

* Fixed documentation errors

## v0.1.1

* Fixed documentation errors
