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
