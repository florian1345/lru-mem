use std::time::Duration;

use criterion::Criterion;

use lru_mem::LruCache;

use rand::Rng;

fn run_insert_benchmark(cache: &mut LruCache<u64, String>, _: &[u64],
        num_inserts: usize) {
    let mut rng = rand::thread_rng();

    for _ in 0..num_inserts {
        let key = rng.gen();
        let value = crate::value();
        cache.insert(key, value).unwrap();
    }
}

pub(crate) fn insert_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert");
    group.sample_size(100).measurement_time(Duration::from_secs(60));
    crate::bench_cache_function(
        &mut group, 64 * 1024, 1000000, run_insert_benchmark);
    crate::bench_cache_function(
        &mut group, 256 * 1024, 1000000, run_insert_benchmark);
    crate::bench_cache_function(
        &mut group, 1024 * 1024, 1000000, run_insert_benchmark);
    crate::bench_cache_function(
        &mut group, 4 * 1024 * 1024, 1000000, run_insert_benchmark);
    crate::bench_cache_function(
        &mut group, 16 * 1024 * 1024, 1000000, run_insert_benchmark);
    crate::bench_cache_function(
        &mut group, 64 * 1024 * 1024, 1000000, run_insert_benchmark);
}