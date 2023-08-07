use criterion::Criterion;
use rand::Rng;

use crate::bencher_extensions::CacheBenchmarkGroup;

pub(crate) fn remove_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("remove");
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);
    let mut rng = rand::thread_rng();

    for &size in crate::CONSTANT_TIME_SIZES {
        group.bench_with_refilled_cache(&crate::get_id(size), |cache, keys| {
            let key_index = rng.gen_range(0..keys.len());
            cache.remove_entry(&keys[key_index]).unwrap().0
        }, size);
    }
}
