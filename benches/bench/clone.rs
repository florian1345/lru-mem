use std::time::Duration;

use criterion::Criterion;

use lru_mem::LruCache;

use rand::rngs::ThreadRng;

fn run_clone_benchmark(cache: &mut LruCache<u64, String>, _: &[u64],
        _: &mut ThreadRng) {
    let clone = cache.clone();
    assert_eq!(clone.len(), cache.len());
}

pub(crate) fn clone_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("clone");
    group.sample_size(100).measurement_time(Duration::from_secs(60));

    for &size in crate::CONSTANT_TIME_SIZES {
        crate::bench_cache_function(
            &mut group, size, run_clone_benchmark);
    }
}
