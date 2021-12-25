use std::time::Duration;

use criterion::Criterion;

use lru_mem::LruCache;

use rand::rngs::ThreadRng;

fn run_alloc_benchmark(cache: &mut LruCache<u64, String>, _: &[u64],
        _: &mut ThreadRng) {
    cache.shrink_to_fit();
    cache.reserve(cache.capacity());
}

pub(crate) fn alloc_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("alloc");
    group.sample_size(100).measurement_time(Duration::from_secs(60));
    crate::bench_cache_function(
        &mut group, 64 * 1024, run_alloc_benchmark);
    crate::bench_cache_function(
        &mut group, 256 * 1024, run_alloc_benchmark);
    crate::bench_cache_function(
        &mut group, 1024 * 1024, run_alloc_benchmark);
    crate::bench_cache_function(
        &mut group, 4 * 1024 * 1024, run_alloc_benchmark);
    crate::bench_cache_function(
        &mut group, 16 * 1024 * 1024, run_alloc_benchmark);
    crate::bench_cache_function(
        &mut group, 64 * 1024 * 1024, run_alloc_benchmark);
}
