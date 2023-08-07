use criterion::Criterion;

use lru_mem::LruCache;

use crate::bencher_extensions::CacheBenchmarkGroup;

pub(crate) fn alloc_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("alloc");
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);

    for &size in crate::LINEAR_TIME_SIZES {
        group.bench_with_reset_cache(&crate::get_id(size), |cache| {
            cache.reserve(cache.capacity());
        }, LruCache::shrink_to_fit, size);
    }
}
