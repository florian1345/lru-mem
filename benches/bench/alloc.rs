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
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);

    for &size in crate::LINEAR_TIME_SIZES {
        crate::bench_cache_function(
            &mut group, size, run_alloc_benchmark);
    }
}
