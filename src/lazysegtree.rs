use crate::internal_bit::ceil_pow2;
use crate::Monoid;

pub trait MapMonoid<M: Monoid>: Monoid {
    fn mapping(f: &Self::S, x: &M::S) -> M::S;
}

impl<F, M> Default for LazySegtree<F, M>
where
    M: Monoid,
    F: MapMonoid<M>,
{
    fn default() -> Self {
        Self::new(0)
    }
}
impl<F, M> LazySegtree<F, M>
where
    M: Monoid,
    F: MapMonoid<M>,
{
    pub fn new(n: usize) -> Self {
        vec![M::identity(); n].into()
    }
}

impl<F, M> From<Vec<M::S>> for LazySegtree<F, M>
where
    M: Monoid,
    F: MapMonoid<M>,
{
    fn from(v: Vec<M::S>) -> Self {
        let n = v.len();
        let log = ceil_pow2(n as u32) as usize;
        let size = 1 << log;
        let mut d = vec![M::identity(); 2 * size];
        let lz = vec![F::identity(); size];
        d[size..(size + n)].clone_from_slice(&v);
        let mut ret = LazySegtree {
            n,
            size,
            log,
            d,
            lz,
        };
        for i in (1..size).rev() {
            ret.update(i);
        }
        ret
    }
}

impl<F, M> LazySegtree<F, M>
where
    M: Monoid,
    F: MapMonoid<M>,
{
    pub fn set(&mut self, mut p: usize, x: M::S) {
        assert!(p < self.n);
        p += self.size;
        for i in (1..=self.log).rev() {
            self.push(p >> i);
        }
        self.d[p] = x;
        for i in 1..=self.log {
            self.update(p >> i);
        }
    }

    pub fn get(&mut self, mut p: usize) -> M::S {
        assert!(p < self.n);
        p += self.size;
        for i in (1..=self.log).rev() {
            self.push(p >> i);
        }
        self.d[p].clone()
    }

    pub fn prod(&mut self, mut l: usize, mut r: usize) -> M::S {
        assert!(l <= r && r <= self.n);
        if l == r {
            return M::identity();
        }

        l += self.size;
        r += self.size;

        for i in (1..=self.log).rev() {
            if ((l >> i) << i) != l {
                self.push(l >> i);
            }
            if ((r >> i) << i) != r {
                self.push(r >> i);
            }
        }

        let mut sml = M::identity();
        let mut smr = M::identity();
        while l < r {
            if l & 1 != 0 {
                sml = M::binary_operation(&sml, &self.d[l]);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                smr = M::binary_operation(&self.d[r], &smr);
            }
            l >>= 1;
            r >>= 1;
        }

        M::binary_operation(&sml, &smr)
    }

    pub fn all_prod(&self) -> M::S {
        self.d[1].clone()
    }

    pub fn apply(&mut self, mut p: usize, f: F::S) {
        assert!(p < self.n);
        p += self.size;
        for i in (1..=self.log).rev() {
            self.push(p >> i);
        }
        self.d[p] = F::mapping(&f, &self.d[p]);
        for i in 1..=self.log {
            self.update(p >> i);
        }
    }
    pub fn apply_range(&mut self, mut l: usize, mut r: usize, f: F::S) {
        assert!(l <= r && r <= self.n);
        if l == r {
            return;
        }

        l += self.size;
        r += self.size;

        for i in (1..=self.log).rev() {
            if ((l >> i) << i) != l {
                self.push(l >> i);
            }
            if ((r >> i) << i) != r {
                self.push((r - 1) >> i);
            }
        }

        {
            let l2 = l;
            let r2 = r;
            while l < r {
                if l & 1 != 0 {
                    self.all_apply(l, f.clone());
                    l += 1;
                }
                if r & 1 != 0 {
                    r -= 1;
                    self.all_apply(r, f.clone());
                }
                l >>= 1;
                r >>= 1;
            }
            l = l2;
            r = r2;
        }

        for i in 1..=self.log {
            if ((l >> i) << i) != l {
                self.update(l >> i);
            }
            if ((r >> i) << i) != r {
                self.update((r - 1) >> i);
            }
        }
    }

    pub fn max_right<G>(&mut self, mut l: usize, g: G) -> usize
    where
        G: Fn(M::S) -> bool,
    {
        assert!(l <= self.n);
        assert!(g(M::identity()));
        if l == self.n {
            return self.n;
        }
        l += self.size;
        for i in (1..=self.log).rev() {
            self.push(l >> i);
        }
        let mut sm = M::identity();
        while {
            // do
            while l % 2 == 0 {
                l >>= 1;
            }
            if !g(M::binary_operation(&sm, &self.d[l])) {
                while l < self.size {
                    self.push(l);
                    l *= 2;
                    let res = M::binary_operation(&sm, &self.d[l]);
                    if g(res.clone()) {
                        sm = res;
                        l += 1;
                    }
                }
                return l - self.size;
            }
            sm = M::binary_operation(&sm, &self.d[l]);
            l += 1;
            //while
            {
                let l = l as isize;
                (l & -l) != l
            }
        } {}
        self.n
    }

    pub fn min_left<G>(&mut self, mut r: usize, g: G) -> usize
    where
        G: Fn(M::S) -> bool,
    {
        assert!(r <= self.n);
        assert!(g(M::identity()));
        if r == 0 {
            return 0;
        }
        r += self.size;
        for i in (1..=self.log).rev() {
            self.push((r - 1) >> i);
        }
        let mut sm = M::identity();
        while {
            // do
            r -= 1;
            while r > 1 && r % 2 != 0 {
                r >>= 1;
            }
            if !g(M::binary_operation(&self.d[r], &sm)) {
                while r < self.size {
                    self.push(r);
                    r = 2 * r + 1;
                    let res = M::binary_operation(&self.d[r], &sm);
                    if g(res.clone()) {
                        sm = res;
                        r -= 1;
                    }
                }
                return r + 1 - self.size;
            }
            sm = M::binary_operation(&self.d[r], &sm);
            // while
            {
                let r = r as isize;
                (r & -r) != r
            }
        } {}
        0
    }
}

pub struct LazySegtree<F, M>
where
    M: Monoid,
    F: MapMonoid<M>,
{
    n: usize,
    size: usize,
    log: usize,
    d: Vec<M::S>,
    lz: Vec<F::S>,
}
impl<F, M> LazySegtree<F, M>
where
    M: Monoid,
    F: MapMonoid<M>,
{
    fn update(&mut self, k: usize) {
        self.d[k] = M::binary_operation(&self.d[2 * k], &self.d[2 * k + 1]);
    }
    fn all_apply(&mut self, k: usize, f: F::S) {
        self.d[k] = F::mapping(&f, &self.d[k]);
        if k < self.size {
            self.lz[k] = F::binary_operation(&f, &self.lz[k]);
        }
    }
    fn push(&mut self, k: usize) {
        self.all_apply(2 * k, self.lz[k].clone());
        self.all_apply(2 * k + 1, self.lz[k].clone());
        self.lz[k] = F::identity();
    }
}

// TODO is it useful?
use std::fmt::{Debug, Error, Formatter, Write};
impl<F, M> Debug for LazySegtree<F, M>
where
    M: Monoid,
    F: MapMonoid<M>,
    F::S: Debug,
    M::S: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        for i in 0..self.log {
            for j in 0..1 << i {
                f.write_fmt(format_args!(
                    "{:?}[{:?}]\t",
                    self.d[(1 << i) + j],
                    self.lz[(1 << i) + j]
                ))?;
            }
            f.write_char('\n')?;
        }
        for i in 0..self.size {
            f.write_fmt(format_args!("{:?}\t", self.d[self.size + i]))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{Additive, LazySegtree, MapMonoid, Max};
    use proptest::prelude::*;
    use std::cmp::max;

    impl MapMonoid<Max<i32>> for Additive<i32> {
        fn mapping(&f: &i32, &x: &i32) -> i32 {
            f + x
        }
    }

    #[derive(Debug)]
    struct Case0<T> {
        base: Vec<T>,
        apply_range_queries: Vec<(usize, usize, T)>,
        prod_queries: Vec<(usize, usize)>,
    }
    fn case0(max_len: usize, max_q: usize) -> impl Strategy<Value = Case0<i32>> {
        (1..max_len, 1..max_q).prop_flat_map(|(n, q)| {
            let vrange = -1000..1000;
            let base = prop::collection::vec(vrange.clone(), n);
            let apply_range_queries = prop::collection::vec(
                (0..n, 0..=n, vrange)
                    .prop_map(|(x, y, z)| if x > y { (y, x, z) } else { (x, y, z) }),
                q,
            );
            let prod_queries = prop::collection::vec(
                (0..n, 0..=n).prop_map(|(x, y)| if x > y { (y, x) } else { (x, y) }),
                q,
            );
            (base, apply_range_queries, prod_queries).prop_map(|(x, y, z)| Case0 {
                base: x,
                apply_range_queries: y,
                prod_queries: z,
            })
        })
    }
    proptest! {
        #[test]
        fn proptest_max_add_lazy_segtree(
            Case0 {
                mut base,
                apply_range_queries,
                prod_queries,
            } in case0(500,10)
        ) {
            let mut segtree: LazySegtree<Additive<_>, Max<_>> = base.clone().into();
            for ((l0, r0, v), (l1, r1)) in apply_range_queries.into_iter().zip(prod_queries) {
                for i in l0..r0 {
                    base[i] += v;
                }
                segtree.apply_range(l0, r0, v);
                assert_eq!(
                    base[l1..r1].iter().cloned().max().unwrap_or(std::i32::MIN),
                    segtree.prod(l1, r1)
                );
            }
        }
    }

    #[test]
    fn test_max_add_lazy_segtree() {
        let base = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3];
        let n = base.len();
        let mut segtree: LazySegtree<Additive<_>, Max<_>> = base.clone().into();
        check_segtree(&base, &mut segtree);

        let mut segtree = LazySegtree::<Additive<_>, Max<_>>::new(n);
        let mut internal = vec![i32::min_value(); n];
        for i in 0..n {
            segtree.set(i, base[i]);
            internal[i] = base[i];
            check_segtree(&internal, &mut segtree);
        }

        segtree.set(6, 5);
        internal[6] = 5;
        check_segtree(&internal, &mut segtree);

        segtree.apply(5, 1);
        internal[5] += 1;
        check_segtree(&internal, &mut segtree);

        segtree.set(6, 0);
        internal[6] = 0;
        check_segtree(&internal, &mut segtree);

        segtree.apply_range(3, 8, 2);
        internal[3..8].iter_mut().for_each(|e| *e += 2);
        check_segtree(&internal, &mut segtree);
    }

    //noinspection DuplicatedCode
    fn check_segtree(base: &[i32], segtree: &mut LazySegtree<Additive<i32>, Max<i32>>) {
        let n = base.len();
        #[allow(clippy::needless_range_loop)]
        for i in 0..n {
            assert_eq!(segtree.get(i), base[i]);
        }
        for i in 0..=n {
            for j in i..=n {
                assert_eq!(
                    segtree.prod(i, j),
                    base[i..j].iter().max().copied().unwrap_or(i32::min_value())
                );
            }
        }
        assert_eq!(
            segtree.all_prod(),
            base.iter().max().copied().unwrap_or(i32::min_value())
        );
        for k in 0..=10 {
            let f = |x| x < k;
            for i in 0..=n {
                assert_eq!(
                    Some(segtree.max_right(i, f)),
                    (i..=n)
                        .filter(|&j| f(base[i..j]
                            .iter()
                            .max()
                            .copied()
                            .unwrap_or(i32::min_value())))
                        .max()
                );
            }
            for j in 0..=n {
                assert_eq!(
                    Some(segtree.min_left(j, f)),
                    (0..=j)
                        .filter(|&i| f(base[i..j]
                            .iter()
                            .max()
                            .copied()
                            .unwrap_or(i32::min_value())))
                        .min()
                );
            }
        }
    }
}
