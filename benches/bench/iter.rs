use criterion::Criterion;

use crate::bencher_extensions::CacheBenchmarkGroup;

pub(crate) fn iter_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter");
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);

    for &size in crate::LINEAR_TIME_SIZES {
        group.bench_with_cache(&crate::get_id(size), |cache, _| {
            for entry in cache.iter() {
                criterion::black_box(entry);
            }
        }, size);
    }
}
