use std::iter::{self, Empty, Once};
use std::time::{Duration, Instant};
use std::vec::IntoIter as VecIntoIter;

use criterion::BenchmarkGroup;
use criterion::measurement::WallTime;
use rand::Rng;

use lru_mem::LruCache;

pub(crate) trait KeysToRestore {
    type KeyIter: Iterator<Item = String>;

    fn keys(self) -> Self::KeyIter;
}

impl KeysToRestore for () {
    type KeyIter = Empty<String>;

    fn keys(self) -> Empty<String> {
        iter::empty()
    }
}

impl KeysToRestore for String {
    type KeyIter = Once<String>;

    fn keys(self) -> Once<String> {
        iter::once(self)
    }
}

impl KeysToRestore for Vec<String> {
    type KeyIter = VecIntoIter<String>;

    fn keys(self) -> VecIntoIter<String> {
        self.into_iter()
    }
}

/// A trait with cache-related extensions for [BenchmarkGroup].
pub(crate) trait CacheBenchmarkGroup {

    /// Benchmarks the given `routine`, which is supplied with a reset
    /// `LruCache` with `size` elements on each iteration. After each iteration,
    /// the given `reset` function is called to reset the cache in a use-case
    /// specific manner. This prevents redundant cleanup steps for certain
    /// benchmarks.
    fn bench_with_reset_cache<O, Rou, Res>(&mut self, routine: Rou, reset: Res,
        size: usize)
    where
        Rou: FnMut(&mut LruCache<String, String>) -> O,
        Res: FnMut(&mut LruCache<String, String>);

    /// Benchmarks the given `routine`, which is supplied with a `LruCache` of
    /// with `size` elements on each iteration. As a second argument, a slice of
    /// all initial keys is provided. The cache is not repaired in any way after
    /// an iteration, so it is the routine's responsibility no to change the key
    /// set.
    fn bench_with_cache<O, R>(&mut self, routine: R, size: usize)
    where
        R: FnMut(&mut LruCache<String, String>, &[String]) -> O;

    /// Benchmarks the given `routine`, which is supplied with a mutable
    /// reference to the same `LruCache` on each iteration. Initially, the cache
    /// is filled to the given `size`. After each iteration, every removed key,
    /// as indicated by the [KeysToRestore] return value of the routine, is
    /// restored. As a second argument, the routine gets a slice of all keys.
    fn bench_with_refilled_cache<O, R>(&mut self, routine: R, size: usize)
    where
        O: KeysToRestore,
        R: FnMut(&mut LruCache<String, String>, &[String]) -> O;

    /// Benchmarks the given `routine`, which is supplied with a mutable
    /// reference to the same `LruCache` on each iteration. Should the size of
    /// the cache be greater than `max_size` after any iteration, it will be
    /// depleted to `min_size` elements before the next iteration. The initial
    /// size of the cache is `min_size`.
    fn bench_with_depleted_cache<O, R>(&mut self, routine: R, min_size: usize,
        max_size: usize)
    where
        R: FnMut(&mut LruCache<String, String>) -> O;
}

fn gen_key(rng: &mut impl Rng) -> String {
    let num = rng.gen::<u64>();
    format!("{:016x}", num)
}

fn gen_value() -> String {
    const VALUE_LEN: usize = 16;

    let mut bytes = vec![b'0'; VALUE_LEN];
    bytes.shrink_to_fit();
    String::from_utf8(bytes).unwrap()
}

fn fill_to_size(cache: &mut LruCache<String, String>, size: usize) {
    let mut rng = rand::thread_rng();

    while cache.len() < size {
        cache.insert(gen_key(&mut rng), gen_value()).unwrap();
    }
}

fn deplete_to_size(cache: &mut LruCache<String, String>, size: usize) {
    let mut rng = rand::thread_rng();
    let keys = cache.keys().cloned().collect::<Vec<_>>();

    while cache.len() > size {
        let key_index = rng.gen_range(0..keys.len());
        cache.remove(&keys[key_index]);
    }
}

fn restore_keys<K>(cache: &mut LruCache<String, String>, keys_to_restore: K)
where
    K: KeysToRestore
{
    for key in keys_to_restore.keys() {
        cache.insert(key, gen_value()).unwrap();
    }
}

impl<'a> CacheBenchmarkGroup for BenchmarkGroup<'a, WallTime> {

    fn bench_with_reset_cache<O, Rou, Res>(&mut self, mut routine: Rou,
        mut reset: Res, size: usize)
    where
        Rou: FnMut(&mut LruCache<String, String>) -> O,
        Res: FnMut(&mut LruCache<String, String>)
    {
        let id = crate::get_id(size);
        let mut cache = LruCache::with_capacity(usize::MAX, size);

        self.bench_function(id, |group| group.iter_custom(|iter_count| {
            let mut total = Duration::ZERO;

            for _ in 0..iter_count {
                reset(&mut cache);
                fill_to_size(&mut cache, size);

                let start = Instant::now();
                routine(&mut cache);
                total += start.elapsed();
            }

            total
        }));
    }

    fn bench_with_cache<O, R>(&mut self, mut routine: R, size: usize)
    where
        R: FnMut(&mut LruCache<String, String>, &[String]) -> O
    {
        let id = crate::get_id(size);
        let mut cache = LruCache::with_capacity(usize::MAX, size);
        fill_to_size(&mut cache, size);
        let keys = cache.keys().cloned().collect::<Vec<_>>();

        self.bench_function(id, |group| group.iter(|| routine(&mut cache, &keys)));
    }

    fn bench_with_refilled_cache<O, R>(&mut self, mut routine: R, size: usize)
    where
        O: KeysToRestore,
        R: FnMut(&mut LruCache<String, String>, &[String]) -> O
    {
        let id = crate::get_id(size);
        let mut cache = LruCache::with_capacity(usize::MAX, size);
        fill_to_size(&mut cache, size);
        let keys = cache.keys().cloned().collect::<Vec<_>>();

        self.bench_function(id, |bencher| bencher.iter_custom(|iter_count| {
            let mut completed = 0;
            let mut total = Duration::ZERO;

            loop {
                let before = Instant::now();
                let keys_to_restore = routine(&mut cache, &keys);
                total += before.elapsed();

                restore_keys(&mut cache, keys_to_restore);
                completed += 1;

                if completed >= iter_count {
                    return total;
                }
            }
        }));
    }

    fn bench_with_depleted_cache<O, R>(&mut self, mut routine: R,
        min_size: usize, max_size: usize)
    where
        R: FnMut(&mut LruCache<String, String>) -> O
    {
        let id = crate::get_id(max_size);
        let mut cache = LruCache::with_capacity(usize::MAX, max_size);
        fill_to_size(&mut cache, min_size);

        self.bench_function(id, |bencher| bencher.iter_custom(|iter_count| {
            let mut completed = 0;
            let mut total = Duration::ZERO;
            let mut last_depletion = Instant::now();

            loop {
                routine(&mut cache);

                completed += 1;

                if completed >= iter_count {
                    return total + last_depletion.elapsed();
                }

                if cache.len() > max_size {
                    total += last_depletion.elapsed();
                    deplete_to_size(&mut cache, min_size);
                    last_depletion = Instant::now();
                }
            }
        }));
    }
}
