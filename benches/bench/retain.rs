use criterion::Criterion;

use lru_mem::LruCache;

use rand::rngs::ThreadRng;

fn run_retain_benchmark(cache: &mut LruCache<u64, String>, _: &[u64],
        _: &mut ThreadRng) {
    cache.retain(|k, v| (*k + v.len() as u64) % 2 == 0);
}

pub(crate) fn retain_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("retain");
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);

    for &size in crate::LINEAR_TIME_SIZES {
        crate::bench_cache_function_with_refill(
            &mut group, size, run_retain_benchmark);
    }
}
