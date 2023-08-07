use criterion::Criterion;
use rand::Rng;

use crate::bencher_extensions::CacheBenchmarkGroup;

pub(crate) fn peek_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("peek");
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);
    let mut rng = rand::thread_rng();

    for &size in crate::CONSTANT_TIME_SIZES {
        let id = crate::get_id(size);

        group.bench_with_cache(&id, |cache, keys| {
            let key_index = rng.gen_range(0..keys.len());
            cache.peek(&keys[key_index]);
        }, size);
    }
}
