use std::collections::HashMap;
use criterion::{criterion_group, criterion_main, Criterion};
use rand::distr::Alphanumeric;
use rand::Rng;
use flat_hash_map::FlatHashMap;

fn rand_str() -> String {
    rand::thread_rng()
        .sample_iter(&Alphanumeric)
        .take(20)
        .map(char::from)
        .collect::<String>()
}

fn add_and_rem<M: Extend<(String, usize)>>(map: M, strs: &Vec<String>, remove: impl Fn(&mut M, &String)) {
    let mut map = map;

    for (i, str) in strs.iter().enumerate() {
        map.extend([(str.clone(), i)].into_iter());
    }

    for str in strs.iter() {
        remove(&mut map, str);
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    let all_strs = (0..1_000)
        .map(|_| rand_str())
        .collect::<Vec<String>>();

    let mut group = c.benchmark_group("add & remove 1_000");

    group.bench_with_input("FlatHashMap", &all_strs,|b, i| b.iter(||
        add_and_rem::<FlatHashMap<String, usize>>(FlatHashMap::default(),
                                                  i,
                                                  |map, key| { map.remove(key); })));

    group.bench_with_input("HashMap", &all_strs, |b, i| b.iter(||
        add_and_rem::<HashMap<String, usize>>(HashMap::default(),
                                              i,
                                              |map, key| { map.remove(key); })));

    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);