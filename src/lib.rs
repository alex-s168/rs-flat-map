use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher, Hash};
use std::{fmt, mem};
use std::fmt::Debug;
use std::mem::MaybeUninit;
use std::ops::Index;

pub struct FlatHashMap<K: Hash + PartialOrd, V, S: BuildHasher = BuildHasherDefault<DefaultHasher>> {
    hasher: S,
    num_buckets: usize,
    num_chunks: usize,

    hashes: Vec<u64>,
    keys: Vec<MaybeUninit<K>>,
    values: Vec<MaybeUninit<V>>,
}

macro_rules! comp_asserts {
    ($self: expr) => {
        if $self.keys.len() != $self.hashes.len() {
            std::unreachable!();
        }
        if $self.values.len() != $self.hashes.len() {
            std::unreachable!();
        }
        if $self.keys.len() != $self.values.len() {
            std::unreachable!();
        }
    }
}

// TODO: dealloc empty chunks
// TODO: auto realloc to increase buckets

const DEFAULT_BUCKETS: usize = 128;
const BUCKET_CHUNK_LEN: usize = 16;
type BucketChunkBools = u16;

impl<K: Hash + PartialOrd, V, S: BuildHasher> FlatHashMap<K, V, S> {
    pub fn with_hasher_and_buckets(hasher: S, buckets: usize) -> Self {
        Self {
            hasher,
            num_buckets: buckets,
            num_chunks: 0,
            hashes: vec![],
            keys: vec![],
            values: vec![]
        }
    }
    
    pub fn with_hasher(hasher: S) -> Self {
        Self::with_hasher_and_buckets(hasher, DEFAULT_BUCKETS)
    }
    
    fn compute_idx(&self, bucket: usize, chunk: usize, elt: usize) -> usize {
        (chunk * self.num_buckets + bucket) * BUCKET_CHUNK_LEN + elt
    }

    fn compute_bucket(&self, hash: u64) -> usize {
        if self.num_buckets == 0 {
            unreachable!();        
        }
        ((hash - 1) as usize) % (self.num_buckets)
    }

    fn fix_hash(hash: u64) -> u64 {
        if hash == 0 { hash + 1 } else { hash }
    }

    fn append_chunk(&mut self) {
        comp_asserts!(self);

        let add_elems = self.num_buckets * BUCKET_CHUNK_LEN;

        self.hashes.resize(self.hashes.len() + add_elems, 0);
        self.keys.resize_with(self.keys.len() + add_elems, || MaybeUninit::uninit());
        self.values.resize_with(self.values.len() + add_elems, || MaybeUninit::uninit());

        self.num_chunks += 1;
    }

    fn get_hash(&self, key: &K) -> u64 {
        Self::fix_hash(self.hasher.hash_one(key))
    }

    fn try_delete_at(&mut self, idx: usize) {
        comp_asserts!(self);

        if self.hashes[idx] != 0 {
            self.hashes[idx] = 0;
            unsafe {
                self.keys[idx].assume_init_drop();
                self.values[idx].assume_init_drop();
            };
        }
    }

    fn drop_at(&mut self, idx: usize) -> (K, V) {
        comp_asserts!(self);

        self.hashes[idx] = 0;

        let mut own_key = MaybeUninit::uninit();
        let mut own_val = MaybeUninit::uninit();

        mem::swap(&mut own_key, &mut self.keys[idx]);
        mem::swap(&mut own_val, &mut self.values[idx]);

        unsafe { (own_key.assume_init(), own_val.assume_init()) }
    }

    fn put_at(&mut self, idx: usize, hash: u64, key: K, val: V) {
        comp_asserts!(self);

        self.hashes[idx] = hash;
        self.keys[idx] = MaybeUninit::new(key);
        self.values[idx] = MaybeUninit::new(val);
    }

    fn add(&mut self, hash: u64, key: K, val: V) {
        comp_asserts!(self);

        let bucket = self.compute_bucket(hash);

        // is there empty space in the last chunk?
        if self.num_chunks > 0 {
            let begin_idx = self.compute_idx(bucket, self.num_chunks - 1, 0);
            for i in begin_idx..(begin_idx + BUCKET_CHUNK_LEN) {
                if self.hashes[i] == 0 {
                    self.put_at(i, hash, key, val);
                    return;
                }
            }
        }

        // otherwise append chunk
        let begin_idx = self.compute_idx(bucket, self.num_chunks, 0);
        self.append_chunk();

        self.put_at(begin_idx, hash, key, val);
    }

    fn get_idx(&self, hash: u64, key: &K) -> Option<usize> {
        comp_asserts!(self);

        let bucket = self.compute_bucket(hash);

        let mut first = None;
        for chunk in 0..self.num_chunks {
            let idx_begin = self.compute_idx(bucket, chunk, 0);
            
            let mut where_hash_eq: BucketChunkBools = 0;
            for item in 0..BUCKET_CHUNK_LEN {
                let idx = idx_begin.wrapping_add(item);
                where_hash_eq |= (if unsafe { *self.hashes.get_unchecked(idx) } == hash { 1 } else { 0 }) << item;
            }
            
            if where_hash_eq != 0 {
                if let Some(first_match_idx) = first {
                    if unsafe { *(*self.keys.get_unchecked(first_match_idx as usize)).as_ptr() == *key } {
                        return Some(first_match_idx);
                    }
                    first = None;
                }
                
                let ones = where_hash_eq.count_ones();
                if ones > 1 {
                    for item in 0..BUCKET_CHUNK_LEN {
                        let idx = idx_begin.wrapping_add(item);
                        let keyptr = unsafe { (*self.keys.get_unchecked(idx)).as_ptr() };
                        if (where_hash_eq & (1 << item)) != 0 && unsafe { *keyptr == *key } {
                            return Some(idx);
                        }
                    }
                }
                else {
                    first = Some(idx_begin + where_hash_eq.trailing_zeros() as usize);
                }
            }
        }

        if let Some(first_match_idx) = first {
            if unsafe { *(*self.keys.get_unchecked(first_match_idx)).as_ptr() == *key } {
                return Some(first_match_idx);
            }
        }
        
        return None
    }

    fn get_at(&self, idx: usize) -> (&K, &V) {
        comp_asserts!(self);

        unsafe {
            (
                &*self.keys[idx].as_ptr(),
                &*self.values[idx].as_ptr()
            )
        }
    }

    pub fn contains(&self, key: &K) -> bool {
        self.get_idx(self.get_hash(key), key).is_some()
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        self.get_idx(self.get_hash(key), key)
            .map(|idx| self.get_at(idx).1)
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        self.get_idx(self.get_hash(key), key)
            .map(|idx| {
                self.drop_at(idx).1
            })
    }

    pub fn put(&mut self, key: K, val: V) {
        let hash = self.get_hash(&key);

        if let Some(idx) = self.get_idx(hash, &key) {
            self.try_delete_at(idx);
            self.put_at(idx, hash, key, val);
        }
        else {
            self.add(hash, key, val);
        }
    }

    pub fn iter(&self) -> Iter<K, V, S> {
        (&self).into_iter()
    }

    pub fn count(&self) -> usize {
        self.iter().count()
    }
}

impl<K: Hash + PartialOrd, V> FlatHashMap<K, V, BuildHasherDefault<DefaultHasher>> {
    pub fn with_buckets(num_buckets: usize) -> Self {
        Self::with_hasher_and_buckets(BuildHasherDefault::default(), num_buckets)
    }
}

impl<K: Hash + PartialOrd, V> Default for FlatHashMap<K, V, BuildHasherDefault<DefaultHasher>> {
    fn default() -> Self {
        Self::with_buckets(DEFAULT_BUCKETS)
    }
}

impl<K: Hash + PartialOrd, V, H: BuildHasher> Drop for FlatHashMap<K, V, H> {
    fn drop(&mut self) {
        comp_asserts!(self);
        for i in 0..self.hashes.len() {
            self.try_delete_at(i);
        }
        self.hashes.clear();
        self.keys.clear();
        self.values.clear();
    }
}

impl<K: Hash + PartialOrd, V, H: BuildHasher> IntoIterator for FlatHashMap<K, V, H> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, H>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter { map: self, idx: 0 }
    }
}

pub struct IntoIter<K: Hash + PartialOrd, V, H: BuildHasher> {
    map: FlatHashMap<K, V, H>,
    idx: usize,
}

impl<K: Hash + PartialOrd, V, H: BuildHasher> Iterator for IntoIter<K, V, H> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let idx = self.idx;
            self.idx += 1;

            if idx >= self.map.hashes.len() {
                break None;
            }

            if self.map.hashes[idx] != 0 {
                break Some(self.map.drop_at(idx));
            }
        }
    }
}

pub struct Iter<'a, K: Hash + PartialOrd, V, H: BuildHasher> {
    parent: &'a FlatHashMap<K, V, H>,
    idx: usize,
}

impl<'a, K: Hash + PartialOrd, V, H: BuildHasher> Iterator for Iter<'a, K, V, H> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let idx = self.idx;
            self.idx += 1;

            if idx >= self.parent.hashes.len() {
                break None;
            }

            if self.parent.hashes[idx] != 0 {
                break Some(self.parent.get_at(idx));
            }
        }
    }
}

impl<K: Hash + PartialOrd, V, H: BuildHasher> Extend<(K, V)> for FlatHashMap<K, V, H> {
    fn extend<T: IntoIterator<Item=(K, V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.put(k, v);
        }
    }
}

impl<'a, K: Hash + PartialOrd + Copy, V: Copy, H: BuildHasher> Extend<(&'a K, &'a V)> for FlatHashMap<K, V, H> {
    fn extend<T: IntoIterator<Item=(&'a K, &'a V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.put(*k, *v);
        }
    }
}

impl<'a, K: Hash + PartialOrd, V, H: BuildHasher> IntoIterator for &'a FlatHashMap<K, V, H> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V, H>;

    fn into_iter(self) -> Self::IntoIter {
        Iter { parent: self, idx: 0 }
    }
}

impl<K: Hash + PartialOrd + Debug, V: Debug, H: BuildHasher> Debug for FlatHashMap<K, V, H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: Hash + PartialOrd, V, H: BuildHasher> Index<&K> for FlatHashMap<K, V, H> {
    type Output = V;
    fn index(&self, key: &K) -> &Self::Output {
        self.get(key).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use rand::distr::Alphanumeric;
    use rand::Rng;
    use super::*;

    fn rand_str() -> String {
        rand::thread_rng()
            .sample_iter(&Alphanumeric)
            .take(7)
            .map(char::from)
            .collect::<String>()
    }
    
    #[test]
    fn append_and_remove() {
        let all_strs = (0..500)
            .map(|_| rand_str())
            .collect::<Vec<String>>();

        let mut map = FlatHashMap::<String, usize>::default();
        
        for (i, str) in all_strs.iter().enumerate() {
            map.put(str.clone(), i);
        }

        assert_eq!(map.count(), all_strs.len());

        for (i, str) in all_strs.iter().enumerate() {
            assert_eq!(map.remove(str).unwrap(), i);
        }

        assert_eq!(map.count(), 0);
    }
}

