use std::time::Duration;

use criterion::Criterion;

use lru_mem::LruCache;

use rand::Rng;
use rand::rngs::ThreadRng;

fn run_get_benchmark(cache: &mut LruCache<u64, String>, keys: &[u64],
        _: &mut ThreadRng) {
    let mut rng = rand::thread_rng();
    let get_index = rng.gen_range(0..keys.len());
    cache.get(&keys[get_index]);
}

pub(crate) fn get_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("get");
    group.sample_size(100).measurement_time(Duration::from_secs(60));

    for &size in crate::LINEAR_TIME_SIZES {
        crate::bench_cache_function(
            &mut group, size, run_get_benchmark);
    }
}
