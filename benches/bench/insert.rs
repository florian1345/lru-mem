use criterion::Criterion;

use crate::bencher_extensions::CacheBenchmarkGroup;

pub(crate) fn insert_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert");
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);

    for &size in crate::CONSTANT_TIME_SIZES {
        let id = crate::get_id(size);
        let mut key_idx: u32 = 0;

        group.bench_with_depleted_cache(&id, |cache| {
            cache.insert(format!("{:08x}", key_idx), String::new()).unwrap();
            key_idx += 1;
        }, size * 7 / 8, size);
    }
}
