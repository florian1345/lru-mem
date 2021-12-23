use std::time::Duration;

use criterion::Criterion;

use lru_mem::LruCache;

use rand::Rng;

fn run_get_benchmark(cache: &mut LruCache<u64, String>, keys: &[u64],
        num_gets: usize) {
    let mut rng = rand::thread_rng();

    for _ in 0..num_gets {
        let get_index = rng.gen_range(0..keys.len());
        cache.get(&keys[get_index]);
    }
}

pub(crate) fn get_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("get");
    group.sample_size(100).measurement_time(Duration::from_secs(60));
    crate::bench_cache_function(
        &mut group, 64 * 1024, 1000000, run_get_benchmark);
    crate::bench_cache_function(
        &mut group, 256 * 1024, 1000000, run_get_benchmark);
    crate::bench_cache_function(
        &mut group, 1024 * 1024, 1000000, run_get_benchmark);
    crate::bench_cache_function(
        &mut group, 4 * 1024 * 1024, 1000000, run_get_benchmark);
    crate::bench_cache_function(
        &mut group, 16 * 1024 * 1024, 1000000, run_get_benchmark);
    crate::bench_cache_function(
        &mut group, 64 * 1024 * 1024, 1000000, run_get_benchmark);
}
