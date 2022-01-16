use crate::LruCache;
use crate::entry::EntryPtr;

use std::iter::FusedIterator;
use std::marker::PhantomData;

/// An iterator over references to the entries of an [LruCache] ordered from
/// least- to most-recently-used. This is obtained by calling [LruCache::iter].
pub struct Iter<'a, K, V> {
    next: EntryPtr<K, V>,
    next_back: EntryPtr<K, V>,
    lifetime: PhantomData<&'a ()>
}

impl<'a, K, V> Iter<'a, K, V> {
    pub(crate) fn new<S>(cache: &LruCache<K, V, S>) -> Iter<K, V> {
        if cache.is_empty() {
            Iter {
                next: unsafe { EntryPtr::null() },
                next_back: unsafe { EntryPtr::null() },
                lifetime: PhantomData
            }
        }
        else {
            Iter {
                next: cache.seal.get().prev,
                next_back: cache.seal.get().next,
                lifetime: PhantomData
            }
        }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.next.is_null() {
            None
        }
        else {
            let entry = unsafe { self.next.get_extended() };

            if self.next == self.next_back {
                self.next = unsafe { EntryPtr::null() };
            }
            else {
                self.next = entry.prev;
            }

            unsafe { Some((entry.key(), entry.value())) }
        }
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        if self.next.is_null() {
            None
        }
        else {
            let entry = unsafe { self.next_back.get_extended() };

            if self.next_back == self.next {
                self.next = unsafe { EntryPtr::null() };
            }
            else {
                self.next_back = entry.next;
            }

            unsafe { Some((entry.key(), entry.value())) }
        }
    }
}

impl<'a, K: 'a, V: 'a> FusedIterator for Iter<'a, K, V> { }

/// An iterator over references to the keys of an [LruCache] ordered from
/// least- to most-recently-used. This is obtained by calling [LruCache::keys].
pub struct Keys<'a, K, V> {
    iter: Iter<'a, K, V>
}

impl<'a, K, V> Keys<'a, K, V> {
    pub(crate) fn new<S>(cache: &'a LruCache<K, V, S>) -> Keys<'a, K, V> {
        Keys {
            iter: Iter::new(cache)
        }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        self.iter.next().map(|(k, _)| k)
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a K> {
        self.iter.next_back().map(|(k, _)| k)
    }
}

impl<'a, K: 'a, V: 'a> FusedIterator for Keys<'a, K, V> { }

/// An iterator over references to the values of an [LruCache] ordered from
/// least- to most-recently-used. This is obtained by calling
/// [LruCache::values].
pub struct Values<'a, K, V> {
    iter: Iter<'a, K, V>
}

impl<'a, K, V> Values<'a, K, V> {
    pub(crate) fn new<S>(cache: &'a LruCache<K, V, S>) -> Values<'a, K, V> {
        Values {
            iter: Iter::new(cache)
        }
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        self.iter.next().map(|(_, v)| v)
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Values<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a V> {
        self.iter.next_back().map(|(_, v)| v)
    }
}

impl<'a, K: 'a, V: 'a> FusedIterator for Values<'a, K, V> { }

struct TakingIterator<K, V> {
    next: EntryPtr<K, V>,
    next_back: EntryPtr<K, V>,
}

impl<K, V> TakingIterator<K, V> {
    fn new<S>(cache: &LruCache<K, V, S>) -> TakingIterator<K, V> {
        if cache.is_empty() {
            TakingIterator {
                next: unsafe { EntryPtr::null() },
                next_back: unsafe { EntryPtr::null() }
            }
        }
        else {
            TakingIterator {
                next: cache.seal.get().prev,
                next_back: cache.seal.get().next
            }
        }
    }
}

impl<K, V> Iterator for TakingIterator<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        if self.next.is_null() {
            None
        }
        else {
            unsafe {
                let entry = self.next.read();

                if self.next == self.next_back {
                    self.next = EntryPtr::null();
                }
                else {
                    self.next = entry.prev;
                }

                Some(entry.into_key_value())
            }
        }
    }
}

impl<K, V> DoubleEndedIterator for TakingIterator<K, V> {
    fn next_back(&mut self) -> Option<(K, V)> {
        if self.next.is_null() {
            None
        }
        else {
            unsafe {
                let entry = self.next_back.read();

                if self.next_back == self.next {
                    self.next = EntryPtr::null();
                }
                else {
                    self.next_back = entry.next;
                }

                Some(entry.into_key_value())
            }
        }
    }
}

/// An iterator that drains key-value-pairs from an [LruCache] ordered from
/// least- to most-recently-used. This is obtained by calling
/// [LruCache::drain].
pub struct Drain<'a, K, V, S> {
    iterator: TakingIterator<K, V>,
    cache: &'a mut LruCache<K, V, S>
}

impl<'a, K, V, S> Drain<'a, K, V, S> {
    pub(crate) fn new(cache: &'a mut LruCache<K, V, S>) -> Drain<'a, K, V, S> {
        Drain {
            iterator: TakingIterator::new(cache),
            cache
        }
    }
}

impl<'a, K, V, S> Iterator for Drain<'a, K, V, S> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.iterator.next()
    }
}

impl<'a, K, V, S> DoubleEndedIterator for Drain<'a, K, V, S> {
    fn next_back(&mut self) -> Option<(K, V)> {
        self.iterator.next_back()
    }
}

impl<'a, K, V, S> Drop for Drain<'a, K, V, S> {
    fn drop(&mut self) {
        // Drop all allocated memory of the remaining elements.

        while let Some(_) = self.next() { }

        // Set the cache as empty.

        self.cache.seal.get_mut().next = self.cache.seal;
        self.cache.seal.get_mut().prev = self.cache.seal;

        self.cache.current_size = 0;
        self.cache.table.clear_no_drop();
    }
}

impl<'a, K, V, S> FusedIterator for Drain<'a, K, V, S> { }

/// An iterator that takes ownership of an [LruCache] and iterates over its
/// entries as key-value-pairs ordered from least- to most-recently-used. This
/// is obtained by calling [IntoIterator::into_iter] on the cache.
pub struct IntoIter<K, V, S> {
    iterator: TakingIterator<K, V>,
    cache: LruCache<K, V, S>
}

impl<K, V, S> IntoIter<K, V, S> {
    pub(crate) fn new(cache: LruCache<K, V, S>) -> IntoIter<K, V, S> {
        IntoIter {
            iterator: TakingIterator::new(&cache),
            cache
        }
    }
}

impl<K, V, S> Iterator for IntoIter<K, V, S> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.iterator.next()
    }
}

impl<K, V, S> DoubleEndedIterator for IntoIter<K, V, S> {
    fn next_back(&mut self) -> Option<(K, V)> {
        self.iterator.next_back()
    }
}

impl<K, V, S> Drop for IntoIter<K, V, S> {
    fn drop(&mut self) {
        // Drop all allocated memory of the remaining elements.
        while let Some(_) = self.next() { }

        // Clear items from the cache without dropping their memory.
        self.cache.table.clear_no_drop();
    }
}

/// An iterator that takes ownership of an [LruCache] and iterates over its
/// keys ordered from least- to most-recently-used. This is obtained by calling
/// [LruCache::into_keys].
pub struct IntoKeys<K, V, S> {
    into_iter: IntoIter<K, V, S>
}

impl<K, V, S> IntoKeys<K, V, S> {
    pub(crate) fn new(cache: LruCache<K, V, S>) -> IntoKeys<K, V, S> {
        IntoKeys {
            into_iter: IntoIter::new(cache)
        }
    }
}

impl<K, V, S> Iterator for IntoKeys<K, V, S>  {
    type Item = K;

    fn next(&mut self) -> Option<K> {
        self.into_iter.next().map(|(k, _)| k)
    }
}

impl<K, V, S> DoubleEndedIterator for IntoKeys<K, V, S> {
    fn next_back(&mut self) -> Option<K> {
        self.into_iter.next_back().map(|(k, _)| k)
    }
}

/// An iterator that takes ownership of an [LruCache] and iterates over its
/// values ordered from least- to most-recently-used. This is obtained by
/// calling [LruCache::into_values].
pub struct IntoValues<K, V, S> {
    into_iter: IntoIter<K, V, S>
}

impl<K, V, S> IntoValues<K, V, S> {
    pub(crate) fn new(cache: LruCache<K, V, S>) -> IntoValues<K, V, S> {
        IntoValues {
            into_iter: IntoIter::new(cache)
        }
    }
}

impl<K, V, S> Iterator for IntoValues<K, V, S>  {
    type Item = V;

    fn next(&mut self) -> Option<V> {
        self.into_iter.next().map(|(_, v)| v)
    }
}

impl<K, V, S> DoubleEndedIterator for IntoValues<K, V, S> {
    fn next_back(&mut self) -> Option<V> {
        self.into_iter.next_back().map(|(_, v)| v)
    }
}
