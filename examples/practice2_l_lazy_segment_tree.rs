#![allow(clippy::many_single_char_names)]
use ac_library_rs::{LazySegtree, MapMonoid, Monoid};
use std::io::Read;
use std::iter;

struct M;
impl Monoid for M {
    type S = (u64, u64, u64);
    fn identity() -> Self::S {
        (0, 0, 0)
    }
    fn binary_operation(&(a, b, c): &Self::S, &(d, e, f): &Self::S) -> Self::S {
        (a + d, b + e, c + f + b * d)
    }
}
struct F;
impl Monoid for F {
    type S = bool;
    fn identity() -> Self::S {
        false
    }
    fn binary_operation(a: &Self::S, b: &Self::S) -> Self::S {
        a ^ b
    }
}
impl MapMonoid<M> for F {
    fn mapping(&f: &Self::S, &(a, b, c): &<M as Monoid>::S) -> <M as Monoid>::S {
        if f {
            // (a + b) * (a + b - 1) / 2 - a * (a - 1) / 2 - b * (b - 1) / 2 - c
            // = a * b - c
            (b, a, a * b - c)
        } else {
            (a, b, c)
        }
    }
}

fn main() {
    let mut buf = String::new();
    std::io::stdin().read_to_string(&mut buf).unwrap();
    let mut input = buf.split_whitespace();

    let n = input.next().unwrap().parse().unwrap();
    let q = input.next().unwrap().parse().unwrap();
    let mut segtree: LazySegtree<F, M> = iter::once((0, 0, 0))
        .chain(input.by_ref().take(n).map(|s| match s {
            "0" => (1, 0, 0),
            "1" => (0, 1, 0),
            _ => panic!(),
        }))
        .collect::<Vec<_>>()
        .into();
    for _ in 0..q {
        let t = input.next().unwrap().parse().unwrap();
        let l = input.next().unwrap().parse().unwrap();
        let r: usize = input.next().unwrap().parse().unwrap();
        match t {
            1 => segtree.apply_range(l, r + 1, true),
            2 => println!("{}", segtree.prod(l, r + 1).2),
            _ => {}
        }
    }
}
