use std::time::Duration;

use criterion::Criterion;

use lru_mem::LruCache;

use rand::Rng;
use rand::rngs::ThreadRng;

fn run_remove_benchmark(cache: &mut LruCache<u64, String>, keys: &[u64],
        _: &mut ThreadRng) {
    let mut rng = rand::thread_rng();
    let remove_index = rng.gen_range(0..keys.len());
    let key = keys[remove_index];
    let value = cache.remove(&key).unwrap();
    cache.insert(key, value).unwrap();
}

pub(crate) fn remove_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("remove");
    group.sample_size(100).measurement_time(Duration::from_secs(60));

    for &size in crate::LINEAR_TIME_SIZES {
        crate::bench_cache_function(
            &mut group, size, run_remove_benchmark);
    }
}
