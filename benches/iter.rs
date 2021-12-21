use std::time::Duration;

use criterion::Criterion;

use lru_mem::LruCache;

use rand::{Rng, SeedableRng};

use rand_xoshiro::Xoshiro256PlusPlus;

fn random_value(key: u64, rng: &mut impl Rng) -> Vec<u64> {
    let len = rng.gen_range(1..20);
    let mut value = Vec::with_capacity(len);
    let mut next = key;

    for _ in 0..len {
        value.push(next);
        next += key;
    }

    value
}

fn run_iter_benchmark(size: usize, num_elements: usize) {
    let mut rng = Xoshiro256PlusPlus::from_seed(rand::thread_rng().gen());
    let mut cache = LruCache::with_capacity(size, size / 100);

    for key in 1..=(num_elements as u64) {
        let value = random_value(key, &mut rng);
        cache.insert(key, value).unwrap();

        let mut prev_key = 0;

        for (&key, _) in cache.iter() {
            assert!(prev_key == 0 || key == prev_key + 1);
            prev_key = key;
        }
    }
}

#[allow(dead_code)]
pub(crate) fn iter_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter");
    group.sample_size(10).measurement_time(Duration::from_secs(10));
    group.bench_function("16 KiB",
        |b| b.iter(|| run_iter_benchmark(16 * 1024, 50000)));
    group.bench_function("64 KiB",
        |b| b.iter(|| run_iter_benchmark(64 * 1024, 50000)));
    group.bench_function("256 KiB",
        |b| b.iter(|| run_iter_benchmark(256 * 1024, 50000)));
    group.bench_function("1 MiB",
        |b| b.iter(|| run_iter_benchmark(1024 * 1024, 50000)));
}
