use criterion::Criterion;

use lru_mem::LruCache;

use rand::Rng;
use rand::rngs::ThreadRng;

fn run_peek_benchmark(cache: &mut LruCache<u64, String>, keys: &[u64],
        _: &mut ThreadRng) {
    let mut rng = rand::thread_rng();
    let get_index = rng.gen_range(0..keys.len());
    cache.peek(&keys[get_index]);
}

pub(crate) fn peek_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("peek");
    group.sample_size(100).measurement_time(crate::BENCH_DURATION);

    for &size in crate::CONSTANT_TIME_SIZES {
        crate::bench_cache_function(
            &mut group, size, run_peek_benchmark);
    }
}
