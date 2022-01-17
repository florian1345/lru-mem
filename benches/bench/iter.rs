use std::time::Duration;

use criterion::Criterion;

use lru_mem::LruCache;

use rand::rngs::ThreadRng;

fn run_iter_benchmark(cache: &mut LruCache<u64, String>, _: &[u64],
        _: &mut ThreadRng) {
    for entry in cache.iter() {
        criterion::black_box(entry);
    }
}

pub(crate) fn iter_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter");
    group.sample_size(100).measurement_time(Duration::from_secs(60));

    for &size in crate::CONSTANT_TIME_SIZES {
        crate::bench_cache_function(
            &mut group, size, run_iter_benchmark);
    }
}
