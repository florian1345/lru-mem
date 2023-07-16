use criterion::{black_box, Criterion};
use lru_mem::HeapSize;
use std::iter;
use crate::get_id_with_suffixes;

fn heap_size_benchmark_with<T, F>(make_value: F, sizes: &[usize], group_name: &str,
    c: &mut Criterion)
where
    T: HeapSize,
    F: Fn() -> T
{
    let mut group = c.benchmark_group(group_name);
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);

    for &size in sizes {
        let value = iter::repeat_with(&make_value).take(size).collect::<Vec<_>>();
        let id = get_id_with_suffixes(size, "", "K", "M", "G");
        group.bench_function(id, |b| b.iter(|| {
            let heap_size = value.heap_size();
            black_box(heap_size);
        }));
    }
}

pub(crate) fn heap_size_benchmark(c: &mut Criterion) {
    heap_size_benchmark_with(|| 0u8, crate::CONSTANT_TIME_SIZES, "heap_size/Vec/u8", c);
    heap_size_benchmark_with(
        || Box::new(0u8), crate::CONSTANT_TIME_SIZES, "heap_size/Vec/Box<u8>", c);
    heap_size_benchmark_with(
        || String::from("hello"), crate::LINEAR_TIME_SIZES, "heap_size/Vec/String", c);
}
