use std::time::Duration;
use criterion::BenchmarkGroup;
use criterion::measurement::WallTime;

use lru_mem::LruCache;

use rand::Rng;
use rand::rngs::ThreadRng;

mod alloc;
mod clone;
mod drain;
mod get;
mod insert;
mod iter;
mod peek;
mod remove;
mod retain;

const VALUE_LEN: usize = 100;

fn value() -> String {
    let mut bytes = vec![b'0'; VALUE_LEN];
    bytes.shrink_to_fit();
    unsafe { String::from_utf8_unchecked(bytes) }
}

const KIBI: usize = 1024;
const MEBI: usize = KIBI * KIBI;
const GIBI: usize = KIBI * MEBI;

fn get_id(size: usize) -> String {
    if size >= GIBI {
        format!("{} GiB", size / GIBI)
    }
    else if size >= MEBI {
        format!("{} MiB", size / MEBI)
    }
    else if size >= KIBI {
        format!("{} KiB", size / KIBI)
    }
    else {
        format!("{} B", size)
    }
}

fn fill(cache: &mut LruCache<u64, String>, rng: &mut impl Rng) -> Vec<u64> {
    let mut added = 0;
    let old_len = cache.len();

    while old_len + added == cache.len() {
        let key = rng.gen();
        let value = value();
        cache.insert(key, value).unwrap();
        added += 1;
    }

    cache.keys().cloned().collect()
}

/// Generates a new LRU cache and also returns its keys as a vector.
fn prepare_benchmark(size: usize)
        -> (String, LruCache<u64, String>, Vec<u64>, ThreadRng) {
    let id = get_id(size);
    let mut rng = rand::thread_rng();
    let mut cache = LruCache::new(size);
    let keys = fill(&mut cache, &mut rng);
    (id, cache, keys, rng)
}

fn bench_cache_function<F>(group: &mut BenchmarkGroup<WallTime>,
    size: usize, run_benchmark: F)
where
    F: Fn(&mut LruCache<u64, String>, &[u64], &mut ThreadRng)
{
    let (id, mut cache, keys, mut rng) = prepare_benchmark(size);

    group.bench_function(id, |b| b.iter(||
        run_benchmark(&mut cache, &keys, &mut rng)));
}

fn bench_cache_function_with_refill<F>(group: &mut BenchmarkGroup<WallTime>,
    size: usize, run_benchmark: F)
where
    F: Fn(&mut LruCache<u64, String>, &[u64], &mut ThreadRng)
{
    let (id, mut cache, mut keys, mut rng) = prepare_benchmark(size);

    // TODO find a solution that does not measure the "fill" function as well.

    group.bench_function(id, |b| b.iter(
        || {
            run_benchmark(&mut cache, &keys, &mut rng);
            keys = fill(&mut cache, &mut rng);
        }));
}

const LINEAR_TIME_SIZES: &'static [usize] = &[
    4 * 1024,
    64 * 1024,
    1024 * 1024,
    16 * 1024 * 1024
];

const CONSTANT_TIME_SIZES: &'static [usize] = &[
    64 * 1024,
    1024 * 1024,
    16 * 1024 * 1024,
    256 * 1024 * 1024
];

const BENCH_DURATION: Duration = Duration::from_secs(15);

criterion::criterion_group!(benches,
    alloc::alloc_benchmark,
    clone::clone_benchmark,
    drain::drain_benchmark,
    get::get_benchmark,
    insert::insert_benchmark,
    iter::iter_benchmark,
    peek::peek_benchmark,
    remove::remove_benchmark,
    retain::retain_benchmark
);
criterion::criterion_main!(benches);
