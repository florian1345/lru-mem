use std::time::Duration;

use criterion::Criterion;

use lru_mem::LruCache;

use rand::rngs::ThreadRng;

fn run_iter_benchmark(cache: &mut LruCache<u64, String>, keys: &[u64],
        _: &mut ThreadRng) {
    for ((k, v), expected_key) in cache.iter().zip(keys.iter()) {
        assert_eq!(expected_key, k);
        assert_eq!(crate::VALUE_LEN, v.len());
    }
}

pub(crate) fn iter_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter");
    group.sample_size(100).measurement_time(Duration::from_secs(60));
    crate::bench_cache_function(
        &mut group, 64 * 1024, run_iter_benchmark);
    crate::bench_cache_function(
        &mut group, 256 * 1024, run_iter_benchmark);
    crate::bench_cache_function(
        &mut group, 1024 * 1024, run_iter_benchmark);
    crate::bench_cache_function(
        &mut group, 4 * 1024 * 1024, run_iter_benchmark);
    crate::bench_cache_function(
        &mut group, 16 * 1024 * 1024, run_iter_benchmark);
    crate::bench_cache_function(
        &mut group, 64 * 1024 * 1024, run_iter_benchmark);
}
