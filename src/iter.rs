use crate::{Entry, LruCache};

use std::iter::FusedIterator;
use std::marker::PhantomData;
use std::ptr;

/// An iterator over references to the entries of an [LruCache] ordered from
/// least- to most-recently-used. This is obtained by calling [LruCache::iter].
pub struct Iter<'a, K, V> {
    next: *mut Entry<K, V>,
    next_back: *mut Entry<K, V>,
    lifetime: PhantomData<&'a ()>
}

impl<'a, K, V> Iter<'a, K, V> {
    pub(crate) fn new<S>(cache: &LruCache<K, V, S>) -> Iter<K, V> {
        Iter {
            next: cache.tail,
            next_back: cache.head,
            lifetime: PhantomData
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
            let entry = unsafe { &*self.next };

            if self.next == self.next_back {
                self.next = ptr::null_mut();
                self.next_back = ptr::null_mut();
            }
            else {
                self.next = entry.prev;
            }

            Some((&entry.key, &entry.value))
        }
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        if self.next_back.is_null() {
            None
        }
        else {
            let entry = unsafe { &*self.next_back };

            if self.next_back == self.next {
                self.next_back = ptr::null_mut();
                self.next = ptr::null_mut();
            }
            else {
                self.next_back = entry.next;
            }

            Some((&entry.key, &entry.value))
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

/// An iterator that drains key-value-pairs from an [LruCache] odered from
/// least- to most-recently-used. This is obtained by calling
/// [LruCache::drain].
pub struct Drain<'a, K, V, S> {
    cache: &'a mut LruCache<K, V, S>
}

impl<'a, K, V, S> Drain<'a, K, V, S> {
    pub(crate) fn new(cache: &'a mut LruCache<K, V, S>) -> Drain<'a, K, V, S> {
        Drain { cache }
    }
}

fn next<K, V, S>(cache: &mut LruCache<K, V, S>) -> Option<(K, V)> {
    if cache.tail.is_null() {
        None
    }
    else {
        unsafe {
            let entry = ptr::read(cache.tail);

            if cache.tail == cache.head {
                cache.tail = ptr::null_mut();
                cache.head = ptr::null_mut();
            }
            else {
                cache.tail = (*cache.tail).prev;
            }

            Some((entry.key, entry.value))
        }
    }
}

fn next_back<K, V, S>(cache: &mut LruCache<K, V, S>) -> Option<(K, V)> {
    if cache.head.is_null() {
        None
    }
    else {
        unsafe {
            let entry = ptr::read(cache.head);

            if cache.head == cache.tail {
                cache.head = ptr::null_mut();
                cache.tail = ptr::null_mut();
            }
            else {
                cache.head = (*cache.head).next;
            }

            Some((entry.key, entry.value))
        }
    }
}

impl<'a, K, V, S> Iterator for Drain<'a, K, V, S> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        next(&mut self.cache)
    }
}

impl<'a, K, V, S> DoubleEndedIterator for Drain<'a, K, V, S> {
    fn next_back(&mut self) -> Option<(K, V)> {
        next_back(&mut self.cache)
    }
}

impl<'a, K, V, S> Drop for Drain<'a, K, V, S> {
    fn drop(&mut self) {
        // Drop all allocated memory of the remaining elements.
        while let Some(_) = self.next() { }

        // Set the cache as empty.
        self.cache.head = ptr::null_mut();
        self.cache.tail = ptr::null_mut();
        self.cache.current_size = 0;
        self.cache.table.clear_no_drop();
    }
}

impl<'a, K, V, S> FusedIterator for Drain<'a, K, V, S> { }

/// An iterator that takes ownership of an [LruCache] and iterates over its
/// entries as key-value-pairs odered from least- to most-recently-used. This
/// is obtained by calling [IntoIterator::into_iter] on the cache.
pub struct IntoIter<K, V, S> {
    cache: LruCache<K, V, S>
}

impl<K, V, S> IntoIter<K, V, S> {
    pub(crate) fn new(cache: LruCache<K, V, S>) -> IntoIter<K, V, S> {
        IntoIter { cache }
    }
}

impl<K, V, S> Iterator for IntoIter<K, V, S> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        next(&mut self.cache)
    }
}

impl<K, V, S> DoubleEndedIterator for IntoIter<K, V, S> {
    fn next_back(&mut self) -> Option<(K, V)> {
        next_back(&mut self.cache)
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
