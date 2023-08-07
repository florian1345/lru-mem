use criterion::{black_box, Criterion};

use crate::bencher_extensions::CacheBenchmarkGroup;

pub(crate) fn drain_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("drain");
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);

    for &size in crate::LINEAR_TIME_SIZES {
        group.bench_with_reset_cache(&crate::get_id(size), |cache| {
            for entry in cache.drain() {
                black_box(entry);
            }
        }, |_| { }, size);
    }
}
