use std::time::Duration;

mod alloc;
mod clone;
mod drain;
mod get;
mod heap_size;
mod insert;
mod iter;
mod peek;
mod remove;
mod retain;
mod bencher_extensions;

const KIBI: usize = 1024;
const MEBI: usize = KIBI * KIBI;
const GIBI: usize = KIBI * MEBI;

pub(crate) fn get_id(size: usize) -> String {
    if size >= GIBI {
        format!("{}G", size / GIBI)
    }
    else if size >= MEBI {
        format!("{}M", size / MEBI)
    }
    else if size >= KIBI {
        format!("{}K", size / KIBI)
    }
    else {
        format!("{}", size)
    }
}

const LINEAR_TIME_SIZES: &'static [usize] = &[
    64,
    1024,
    16 * 1024,
    256 * 1024
];

const CONSTANT_TIME_SIZES: &'static [usize] = &[
    1024,
    16 * 1024,
    256 * 1024,
    4 * 1024 * 1024
];

const BENCH_DURATION: Duration = Duration::from_secs(15);

criterion::criterion_group!(benches,
    alloc::alloc_benchmark,
    clone::clone_benchmark,
    drain::drain_benchmark,
    get::get_benchmark,
    heap_size::heap_size_benchmark,
    insert::insert_benchmark,
    iter::iter_benchmark,
    peek::peek_benchmark,
    remove::remove_benchmark,
    retain::retain_benchmark,
);

criterion::criterion_main!(benches);
