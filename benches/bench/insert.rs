use criterion::Criterion;

use lru_mem::LruCache;

use rand::Rng;
use rand::rngs::ThreadRng;

fn run_insert_benchmark(cache: &mut LruCache<u64, String>, _: &[u64],
        _: &mut ThreadRng) {
    let mut rng = rand::thread_rng();
    let key = rng.gen();
    let value = crate::value();
    cache.insert(key, value).unwrap();
}

pub(crate) fn insert_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert");
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);

    for &size in crate::CONSTANT_TIME_SIZES {
        crate::bench_cache_function(
            &mut group, size, run_insert_benchmark);
    }
}
