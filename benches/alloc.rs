use std::time::Duration;

use criterion::Criterion;

use lru_mem::LruCache;

use rand::{Rng, SeedableRng};

use rand_xoshiro::Xoshiro256PlusPlus;

fn run_alloc_benchmark(size: usize, num_elements: usize) {
    let mut rng = Xoshiro256PlusPlus::from_seed(rand::thread_rng().gen());
    let mut cache = LruCache::with_capacity(size, size / 100);

    for i in 0..num_elements {
        let key: u64 = rng.gen_range(0..1000000000);
        let value: u64 = rng.gen_range(0..1000000000);

        cache.insert(key, value).unwrap();

        match i % 500 {
            100 => cache.reserve(1000),
            200 => cache.shrink_to_fit(),
            300 => cache.try_reserve(400).unwrap(),
            400 => cache.shrink_to(cache.capacity().saturating_sub(800)),
            _ => { }
        }
    }
}

#[allow(dead_code)]
pub(crate) fn alloc_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("alloc");
    group.sample_size(10).measurement_time(Duration::from_secs(10));
    group.bench_function("64 KiB",
        |b| b.iter(|| run_alloc_benchmark(64 * 1024, 200000)));
    group.bench_function("256 KiB",
        |b| b.iter(|| run_alloc_benchmark(256 * 1024, 200000)));
    group.bench_function("1 MiB",
        |b| b.iter(|| run_alloc_benchmark(1024 * 1024, 200000)));
    group.bench_function("4 MiB",
        |b| b.iter(|| run_alloc_benchmark(4 * 1024 * 1024, 200000)));
}
