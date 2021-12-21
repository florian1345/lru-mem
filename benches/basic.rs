use std::time::Duration;

use criterion::Criterion;

use lru_mem::LruCache;

use rand::{Rng, SeedableRng};

use rand_xoshiro::Xoshiro256PlusPlus;

pub(crate) fn random_key(rng: &mut impl Rng) -> String {
    let len: u32 = rng.gen_range(0..1000000);
    let mut string = format!("{:06}", len);
    string.shrink_to_fit();
    string
}

pub(crate) fn random_value(rng: &mut impl Rng) -> String {
    let len = rng.gen_range(0..100);
    let mut bytes = vec![b'0'; len];
    bytes.shrink_to_fit();
    unsafe { String::from_utf8_unchecked(bytes) }
}

fn run_basic_benchmark(size: usize, num_elements: usize) {
    let mut rng = Xoshiro256PlusPlus::from_seed(rand::thread_rng().gen());
    let mut keys = Vec::new();
    let mut cache = LruCache::with_capacity(size, size / 100);

    for _ in 0..num_elements {
        let key = random_key(&mut rng);
        let value = random_value(&mut rng);

        cache.insert(key.clone(), value).unwrap();
        keys.push(key);

        let get_index = rng.gen_range(0..keys.len());
        cache.get(&keys[get_index]);
    }
}

#[allow(dead_code)]
pub(crate) fn basic_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("basic");
    group.sample_size(10).measurement_time(Duration::from_secs(10));
    group.bench_function("64 KiB",
        |b| b.iter(|| run_basic_benchmark(64 * 1024, 1000000)));
    group.bench_function("256 KiB",
        |b| b.iter(|| run_basic_benchmark(256 * 1024, 1000000)));
    group.bench_function("1 MiB",
        |b| b.iter(|| run_basic_benchmark(1024 * 1024, 1000000)));
    group.bench_function("4 MiB",
        |b| b.iter(|| run_basic_benchmark(4 * 1024 * 1024, 1000000)));
    group.bench_function("16 MiB",
        |b| b.iter(|| run_basic_benchmark(16 * 1024 * 1024, 1000000)));
}
