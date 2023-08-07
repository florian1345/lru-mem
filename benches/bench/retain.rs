use criterion::Criterion;
use lru_mem::LruCache;

use crate::bencher_extensions::CacheBenchmarkGroup;

pub(crate) fn retain_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("retain");
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);

    for &size in crate::LINEAR_TIME_SIZES {
        group.bench_with_reset_cache(&crate::get_id(size), |cache| {
            cache.retain(|key, _| key.chars().last().unwrap() != '7');
        }, LruCache::clear, size);
    }
}
