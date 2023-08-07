use criterion::{black_box, Criterion};

use crate::bencher_extensions::CacheBenchmarkGroup;

pub(crate) fn clone_benchmark(c: &mut Criterion) {
    let mut group = crate::make_group(c, "clone");

    for &size in crate::LINEAR_TIME_SIZES {
        group.bench_with_cache(|cache, _| {
            black_box(cache.clone());
        }, size);
    }
}
