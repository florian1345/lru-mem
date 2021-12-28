use super::*;

#[test]
fn tuples_have_correct_size() {
    assert_eq!(12, (1u16, 2u32, 3i16, 'x').mem_size());
    assert_eq!(5, ((1u8, 2i8, 3u8), 4i16).mem_size());
}

#[test]
fn vectors_have_correct_size() {
    let vec_size = mem::size_of::<Vec<u8>>();

    assert_eq!(24 + vec_size,
        vec!['a', 'b', 'c', 'd', 'e', 'f'].mem_size());
    assert_eq!(24 + 4 * vec_size,
        vec![vec![], vec![1u64, 2u64], vec![3u64]].mem_size());

    let mut vec = Vec::with_capacity(8);
    vec.push(1.0f64);

    assert_eq!(64 + vec_size, vec.mem_size());
}

#[test]
fn strings_have_correct_size() {
    let string_size = mem::size_of::<String>();

    assert_eq!(11 + string_size, "hello world".to_owned().mem_size());
    assert_eq!(26 + string_size,
        "söme döüble byte chärs".to_owned().mem_size());
}

#[test]
fn options_have_correct_size() {
    let some = Some(String::from("hello"));
    let none = None::<String>;

    assert_eq!(none.mem_size() + 5, some.mem_size());
}

#[test]
fn entry_correctly_computes_size() {
    let entry = Entry::new("hello".to_owned(), "world!".to_owned());

    let key_str_bytes = 5;
    let value_str_bytes = 6;
    let str_meta_bytes = mem::size_of::<String>();
    let usize_bytes = mem::size_of::<usize>();
    let ptr_bytes = mem::size_of::<*mut Entry<String, String>>();

    // We require key + value (key_str_bytes + value_str_bytes +
    // 2 * str_meta_bytes), 1 usize (size of entry), and 2 pointers (next and
    // prev).

    let expected_bytes = key_str_bytes
        + value_str_bytes
        + 2 * str_meta_bytes
        + usize_bytes
        + 2 * ptr_bytes;

    assert_eq!(expected_bytes, entry.size);
}

#[test]
fn cache_correctly_inserts_with_sufficient_capacity() {
    let mut cache = LruCache::new(1024);

    assert_eq!(0, cache.len());
    assert_eq!(0, cache.current_size());
    assert_eq!(1024, cache.max_size());

    assert_eq!(Ok(None),
        cache.insert("key1".to_owned(), "value1".to_owned()));

    let new_size = cache.current_size();

    assert_eq!(1, cache.len());
    assert!(new_size > 0);
    assert_eq!(Some(&"value1".to_owned()), cache.get("key1"));

    assert_eq!(Ok(None),
        cache.insert("key2".to_owned(), "value2".to_owned()));

    assert_eq!(2, cache.len());
    assert!(cache.current_size() > new_size);
    assert_eq!(Some(&"value1".to_owned()), cache.get("key1"));
    assert_eq!(Some(&"value2".to_owned()), cache.get("key2"));
}

#[test]
fn cache_deduplicates_keys() {
    let mut cache = LruCache::new(1024);

    assert_eq!(Ok(None),
        cache.insert("key".to_owned(), "value".to_owned()));

    let expected_size = cache.current_size;

    assert_eq!(Ok(Some("value".to_owned())),
        cache.insert("key".to_owned(), "value".to_owned()));
    assert_eq!(expected_size, cache.current_size());
    assert_eq!(1, cache.len());
}

fn string_with_size(size: usize) -> String {
    let mut s = String::with_capacity(size);

    for _ in 0..size {
        s.push('0');
    }

    s
}

#[test]
fn cache_ejects_lru_if_overflowing() {
    let mut cache = LruCache::new(2048);

    // On 256-bit arch, each entry requires an extra 289 bytes per entry
    // in addition to the size of the value in bytes (see test case
    // "entry_correctly_computes_size", value_str_bytes = 1).
    // On 16-bit arch, this would be 19 bytes.
    // The numbers in this test case accomodate anywhere from 15 to 696
    // extra bytes (676 * 3 + 15 = 2050, 676 * 2 + 696 = 2048).

    cache.insert("a".to_owned(), string_with_size(676)).unwrap();
    cache.insert("b".to_owned(), string_with_size(676)).unwrap();

    let expected_size = cache.current_size();

    cache.insert("c".to_owned(), string_with_size(676)).unwrap();

    assert_eq!(expected_size, cache.current_size());
    assert_eq!(2, cache.len());
    assert!(cache.get("a").is_none());
    assert!(cache.get("b").is_some());
    assert!(cache.get("c").is_some());

    assert_eq!("b", unsafe { &(*cache.tail).key });
    assert_eq!("c", unsafe { &(*cache.head).key });
}

#[test]
fn getting_sets_most_recently_used() {
    let mut cache = LruCache::new(2048);

    // See the argument why the sizes are like this in test case
    // "cache_ejects_lru_if_overflowing".

    cache.insert("a".to_owned(), string_with_size(674)).unwrap();
    cache.insert("b".to_owned(), string_with_size(674)).unwrap();
    cache.get(&"a".to_owned());
    cache.insert("c".to_owned(), string_with_size(674)).unwrap();

    assert!(cache.get("a").is_some());
    assert!(cache.get("b").is_none());
    assert!(cache.get("c").is_some());

    assert_eq!("a", unsafe { &(*cache.tail).key });
    assert_eq!("c", unsafe { &(*cache.head).key });

    cache.get("a");

    assert_eq!("c", unsafe { &(*cache.tail).key });
    assert_eq!("a", unsafe { &(*cache.head).key });
}

#[test]
fn peeking_does_not_set_most_recently_used() {
    let mut cache = LruCache::new(2048);

    cache.insert("a".to_owned(), string_with_size(674)).unwrap();
    cache.insert("b".to_owned(), string_with_size(674)).unwrap();
    cache.peek(&"a".to_owned());
    cache.insert("c".to_owned(), string_with_size(674)).unwrap();

    assert!(cache.get("a").is_none());
    assert!(cache.get("b").is_some());
    assert!(cache.get("c").is_some());
}

#[test]
fn cache_rejects_too_large_entry() {
    let mut cache = LruCache::new(256);
    let key = "This is a pretty long key, especially considering that keys \
        should normally be rather small to avoid long hashing times.".to_owned();
    let value = "Although the key alone has insufficient size, together with \
        this string it pushes pushes the total memory requirement of the \
        entry over the capacity of the cache.".to_owned();

    assert!(matches!(cache.insert(key, value),
        Err(LruError::EntryTooLarge { .. })));
}

#[test]
fn precisely_fitting_entry_does_not_eject_lru() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello".to_owned(), "world".to_owned()).unwrap();
    cache.insert("greetings".to_owned(), "moon".to_owned()).unwrap();

    let key = "ahoy".to_owned();
    let mut value = "mars".to_owned();
    value.shrink_to_fit();
    let required_size = cache.max_size() - cache.current_size();
    let additional_bytes = required_size - entry_size(&key, &value);
    let additional_data = vec![b's'; additional_bytes];
    value.push_str(&String::from_utf8(additional_data).unwrap());
    value.shrink_to_fit();

    assert_eq!(required_size, entry_size(&key, &value));

    cache.insert(key, value).unwrap();

    assert_eq!(3, cache.len());
}

#[test]
fn removing_works() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", "world").unwrap();
    cache.insert("greetings", "moon").unwrap();
    cache.insert("ahoy", "mars").unwrap();

    assert_eq!(Some(("hello", "world")), cache.remove_entry("hello"));
    assert_eq!(None, cache.remove("hello"));
}

#[test]
fn contains_works() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", "world").unwrap();

    assert!(cache.contains("hello"));
    assert!(!cache.contains("greetings"));
}

#[test]
fn increasing_max_size_keeps_all_elements() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", "world").unwrap();
    cache.insert("greetings", "moon").unwrap();
    cache.set_max_size(2048);

    assert_eq!(2, cache.len());
    assert_eq!(2048, cache.max_size());
}

#[test]
fn decreasing_max_size_below_current_size_drops_elements() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", "world").unwrap();
    cache.insert("greetings", "moon").unwrap();
    cache.set_max_size(cache.current_size() - 1);

    assert_eq!(1, cache.len());
    assert!(cache.current_size() < cache.max_size());
    assert!(cache.max_size() < 1024);
}

#[test]
fn cache_correctly_applies_mutation() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello".to_owned(), "world".to_owned()).unwrap();
    cache.insert("greetings".to_owned(), "moon".to_owned()).unwrap();

    let old_size = cache.current_size();
    let result = cache.mutate("greetings", |s| {
        s.push_str(", from 384400 km away");
        s.shrink_to_fit();
        s.len()
    });

    assert_eq!(Ok(Some(25)), result);
    assert_eq!(2, cache.len());
    assert_eq!(old_size + 21, cache.current_size());
    assert_eq!(Some(&"moon, from 384400 km away".to_owned()),
        cache.get("greetings"));
}

#[test]
fn cache_rejects_too_expanding_mutation() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", vec![0u8; 32]).unwrap();
    cache.insert("greetings", vec![0u8; 32]).unwrap();

    let old_size = cache.current_size();
    let result = cache.mutate("hello", |v| {
        v.append(&mut vec![0u8; 1000]);
    });

    assert!(matches!(result, Err(LruError::EntryTooLarge { .. })));
    assert_eq!(1, cache.len());
    assert!(cache.current_size() < old_size);
    assert_eq!(None, cache.get("hello"));
}

fn test_cache_with_many_accesses<F>(intermediate_op: F)
where
    F: Fn(&mut LruCache<i32, i32>, i32)
{
    let mut cache = LruCache::new(1024);
    cache.insert(0, 0).unwrap();
    let entry_size = cache.current_size();

    for i in 1..=5000 {
        cache.insert(i, i).unwrap();

        for j in 0..=(i / 2) {
            cache.touch(&(j * 2));
        }

        intermediate_op(&mut cache, i);
    }

    let mut found_even = false;

    for i in 0..=1000 {
        let contained = cache.contains(&i);

        if i % 2 == 0 {
            if found_even {
                assert!(contained,
                    "cache did not contain even number {} but contains \
                        lower even number", i);
            }
            else if contained {
                found_even = true;
            }
        }
        else {
            assert!(!contained, "cache contained odd number {}", i);
        }
    }

    assert_eq!(entry_size * cache.len(), cache.current_size());
    assert!(cache.max_size() - cache.current_size() < entry_size);
}

#[test]
fn cache_works_with_many_accesses() {
    test_cache_with_many_accesses(|_, _| { })
}

#[test]
fn reserving_adds_capacity() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", "world").unwrap();
    cache.insert("greetings", "moon").unwrap();
    let additional = cache.capacity() - cache.len() + 5;
    cache.reserve(additional);

    assert!(cache.capacity() >= additional + 2);
    assert!(cache.len() == 2);
    assert_eq!(Some((&"hello", &"world")), cache.peek_lru());
    assert_eq!(Some((&"greetings", &"moon")), cache.peek_mru());

    let additional = additional + 10;

    assert!(cache.try_reserve(additional).is_ok());
    assert!(cache.capacity() >= additional + 2);
}

#[test]
fn reserving_fails_on_overflow() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", "world").unwrap();

    assert!(cache.try_reserve(usize::MAX).is_err());
}

#[test]
fn shrinking_does_not_drop_below_len() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", "world").unwrap();
    cache.insert("greetings", "moon").unwrap();
    cache.insert("ahoy", "mars").unwrap();
    cache.insert("hi", "venus").unwrap();
    cache.insert("good morning", "jupiter").unwrap();
    cache.shrink_to(4);

    assert!(cache.capacity() >= 5);
    assert_eq!(5, cache.len());

    cache.insert("hey", "mercury").unwrap();
    cache.insert("what's up", "saturn").unwrap();
    cache.shrink_to_fit();

    assert!(cache.capacity() >= 7);
    assert_eq!(7, cache.len());
}

#[test]
fn cache_works_with_many_reallocations() {
    test_cache_with_many_accesses(|cache, i| {
        match i % 10 {
            2 => {
                if i > 10 {
                    cache.shrink_to(cache.capacity() - 10)
                }
            },
            4 => cache.reserve(200),
            6 => cache.shrink_to_fit(),
            8 => cache.try_reserve(120).unwrap(),
            _ => { }
        }
    })
}

#[test]
fn iter_works() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", "world").unwrap();
    cache.insert("greetings", "moon").unwrap();
    cache.insert("ahoy", "mars").unwrap();
    cache.insert("hi", "venus").unwrap();
    cache.insert("good morning", "jupiter").unwrap();

    let mut iter = cache.iter();

    assert_eq!(Some((&"hello", &"world")), iter.next());
    assert_eq!(Some((&"good morning", &"jupiter")), iter.next_back());
    assert_eq!(Some((&"hi", &"venus")), iter.next_back());
    assert_eq!(Some((&"ahoy", &"mars")), iter.next_back());
    assert_eq!(Some((&"greetings", &"moon")), iter.next());
    assert_eq!(None, iter.next_back());
    assert_eq!(None, iter.next());
}

#[test]
fn separated_iters_zip_to_pair_iter() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", "world").unwrap();
    cache.insert("greetings", "moon").unwrap();
    cache.insert("ahoy", "mars").unwrap();
    cache.insert("hi", "venus").unwrap();
    cache.insert("good morning", "jupiter").unwrap();

    let pair_iter_collected = cache.iter().collect::<Vec<_>>();
    let zip_iter_collected = cache.keys()
        .zip(cache.values())
        .collect::<Vec<_>>();

    assert_eq!(pair_iter_collected, zip_iter_collected);
}

#[test]
fn drain_clears_cache() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", "world").unwrap();
    cache.insert("greetings", "moon").unwrap();
    cache.drain().next();

    assert_eq!(0, cache.len());
    assert_eq!(0, cache.current_size());
    assert!(cache.get("hello").is_none());
}

#[test]
fn drain_returns_entries() {
    let mut cache = LruCache::new(1024);
    cache.insert("hello", "world").unwrap();
    cache.insert("greetings", "moon").unwrap();
    cache.insert("ahoy", "mars").unwrap();
    cache.insert("hi", "venus").unwrap();
    cache.insert("good morning", "jupiter").unwrap();

    let mut drain = cache.drain();

    assert_eq!(Some(("hello", "world")), drain.next());
    assert_eq!(Some(("good morning", "jupiter")), drain.next_back());
    assert_eq!(Some(("hi", "venus")), drain.next_back());
    assert_eq!(Some(("ahoy", "mars")), drain.next_back());
    assert_eq!(Some(("greetings", "moon")), drain.next());
    assert_eq!(None, drain.next_back());
    assert_eq!(None, drain.next());
}

#[test]
fn clone_creates_independent_cache() {
    let mut cache = LruCache::new(1024);
    cache.insert(0u64, vec![0u8; 32]).unwrap();
    cache.insert(1u64, vec![1u8; 32]).unwrap();

    let mut clone = cache.clone();
    clone.insert(2u64, vec![2u8; 32]).unwrap();
    cache.remove(&0);
    cache.touch(&1);

    assert_eq!(1, cache.len());
    assert_eq!(None, cache.get(&0));
    assert_eq!(Some(&vec![1u8; 32]), cache.get(&1));
    assert_eq!(None, cache.get(&2));

    assert_eq!(3, clone.len());
    assert_eq!(Some(&vec![0u8; 32]), clone.get(&0));
    assert_eq!(Some(&vec![1u8; 32]), clone.get(&1));
    assert_eq!(Some(&vec![2u8; 32]), clone.get(&2));

    assert!(clone.current_size() > cache.current_size());

    let cache_drained = cache.drain().collect::<Vec<_>>();
    let cache_drained_expected = vec![(1, vec![1u8; 32])];
    let clone_drained = clone.drain().collect::<Vec<_>>();
    let clone_drained_expected = vec![
        (0, vec![0u8; 32]),
        (1, vec![1u8; 32]),
        (2, vec![2u8; 32])
    ];

    assert_eq!(cache_drained_expected, cache_drained);
    assert_eq!(clone_drained_expected, clone_drained);
}
