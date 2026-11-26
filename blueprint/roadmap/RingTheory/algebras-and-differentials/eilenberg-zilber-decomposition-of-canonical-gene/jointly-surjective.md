# Every polynomial generator has a nondegenerate ancestor

Let `k` be a commutative ring, `A` a `k`-algebra in carrier universe `max u v`, `T` the
polynomial comonad, and `n : ℕ`. For every `x∈T^n A`, there exist an epimorphism index `a :
[n] → [m]` and `y∈Variables_m` such that `summandIndex k A a y=x`. The set `Variables_m`
consists of indices whose generator points are nondegenerate in the whole underlying
simplicial resolution.
