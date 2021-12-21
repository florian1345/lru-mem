mod alloc;
pub(crate) mod basic;
mod iter;

criterion::criterion_group!(benches,
    alloc::alloc_benchmark,
    basic::basic_benchmark,
    iter::iter_benchmark
);
criterion::criterion_main!(benches);
