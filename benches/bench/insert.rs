use criterion::Criterion;

use crate::bencher_extensions::CacheBenchmarkGroup;

pub(crate) fn insert_benchmark(c: &mut Criterion) {
    let group = crate::make_group(c, "insert");

    for &size in crate::CONSTANT_TIME_SIZES {
        let mut key_idx: u32 = 0;

        group.bench_with_depleted_cache(|cache| {
            cache.insert(format!("{:08x}", key_idx), String::new()).unwrap();
            key_idx += 1;
        }, size * 7 / 8, size);
    }
}
