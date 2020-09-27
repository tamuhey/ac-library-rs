use ac_library_rs::{LazySegtree, MapMonoid, ModInt998244353, Monoid};
use std::io::Read;

type Mint = ModInt998244353;
struct Sum;
impl Monoid for Sum {
    type S = (Mint, usize);

    fn identity() -> Self::S {
        (0.into(), 0)
    }

    fn binary_operation(&(a, n): &Self::S, &(b, m): &Self::S) -> Self::S {
        (a + b, n + m)
    }
}
struct Affine;
impl Monoid for Affine {
    type S = (Mint, Mint);
    fn identity() -> Self::S {
        (1.into(), 0.into())
    }
    fn binary_operation(&(a, b): &Self::S, &(c, d): &Self::S) -> Self::S {
        (a * c, a * d + b)
    }
}
impl MapMonoid<Sum> for Affine {
    fn mapping(&(a, b): &Self::S, &(x, n): &<Sum as Monoid>::S) -> <Sum as Monoid>::S {
        (a * x + b * Mint::new(n), n)
    }
}

#[allow(clippy::many_single_char_names)]
fn main() {
    let mut buf = String::new();
    std::io::stdin().read_to_string(&mut buf).unwrap();
    let mut input = buf.split_whitespace();

    let n = input.next().unwrap().parse().unwrap();
    let q = input.next().unwrap().parse().unwrap();
    let mut segtree: LazySegtree<Affine, Sum> = input
        .by_ref()
        .take(n)
        .map(|s| (s.parse().unwrap(), 1))
        .collect::<Vec<_>>()
        .into();
    for _ in 0..q {
        match input.next().unwrap().parse().unwrap() {
            0 => {
                let l = input.next().unwrap().parse().unwrap();
                let r = input.next().unwrap().parse().unwrap();
                let b = input.next().unwrap().parse().unwrap();
                let c = input.next().unwrap().parse().unwrap();
                segtree.apply_range(l, r, (b, c));
            }
            1 => {
                let l = input.next().unwrap().parse().unwrap();
                let r = input.next().unwrap().parse().unwrap();
                println!("{}", segtree.prod(l, r).0);
            }
            _ => {}
        }
    }
}
