use criterion::BenchmarkGroup;
use criterion::measurement::WallTime;

use lru_mem::LruCache;

use rand::Rng;
use rand::rngs::ThreadRng;

mod alloc;
mod get;
mod insert;
mod iter;
mod peek;

const VALUE_LEN: usize = 100;

fn value() -> String {
    let mut bytes = vec![b'0'; VALUE_LEN];
    bytes.shrink_to_fit();
    unsafe { String::from_utf8_unchecked(bytes) }
}

/// Generates a new LRU cache and also returns its keys as a vector.
fn prepare_cache(size: usize)
        -> (LruCache<u64, String>, Vec<u64>) {
    let mut rng = rand::thread_rng();
    let mut cache = LruCache::new(size);
    let mut added = 0;

    while added == cache.len() {
        let key = rng.gen();
        let value = value();
        cache.insert(key, value).unwrap();
        added += 1;
    }

    let keys = cache.keys().cloned().collect();
    (cache, keys)
}

const KIBI: usize = 1024;
const MEBI: usize = KIBI * KIBI;
const GIBI: usize = KIBI * MEBI;

fn bench_cache_function<F>(group: &mut BenchmarkGroup<WallTime>,
    size: usize, run_benchmark: F)
where
    F: Fn(&mut LruCache<u64, String>, &[u64], &mut ThreadRng)
{
    let id = if size >= GIBI {
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
    };
    let (mut cache, keys) = prepare_cache(size);
    let mut rng = rand::thread_rng();

    group.bench_function(id, |b| b.iter(||
        run_benchmark(&mut cache, &keys, &mut rng)));
}

criterion::criterion_group!(benches,
    alloc::alloc_benchmark,
    get::get_benchmark,
    insert::insert_benchmark,
    iter::iter_benchmark,
    peek::peek_benchmark
);
criterion::criterion_main!(benches);
