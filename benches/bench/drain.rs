use criterion::Criterion;

use lru_mem::LruCache;

use rand::rngs::ThreadRng;

fn run_drain_benchmark(cache: &mut LruCache<u64, String>, _: &[u64],
        _: &mut ThreadRng) {
    for entry in cache.drain() {
        criterion::black_box(entry);
    }
}

pub(crate) fn drain_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("drain");
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);

    for &size in crate::LINEAR_TIME_SIZES {
        crate::bench_cache_function_with_refill(
            &mut group, size, run_drain_benchmark);
    }
}
