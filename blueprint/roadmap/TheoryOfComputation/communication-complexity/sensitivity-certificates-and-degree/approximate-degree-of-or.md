# The approximate degree of OR is Θ(√n)

For $n \ge 1$, the $1/3$-approximate degree of $\mathrm{OR}_n$ satisfies $n \le 6\, \widetilde{\deg}(\mathrm{OR}_n)^2$, and $\widetilde{\deg}(\mathrm{OR}_n) = O(\sqrt n)$.

## Proof sketch

Lower bound: $bs(\mathrm{OR}_n) = n$ (every bit is sensitive at the all-zero input), so Nisan–Szegedy gives $n \le 6 \widetilde\deg^2$. Upper bound: with $u(k) = (n-k)/(n-1)$, the polynomial $Q(k) = 1 - T_d(u(k))/T_d(u(0))$ built from the Chebyshev polynomial $T_d$, which is bounded by $1$ on $[-1,1]$ and grows like $1 + d^2\mu$ at $1 + \mu$, vanishes at $k = 0$ and is within $1/3$ of $1$ for $1 \le k \le n$ once $d = O(\sqrt n)$; compose with the Hamming weight.

## Depends on

- [Approximate degree of a Boolean function](approximate-degree-of-a-boolean-function.md)

## Proof depends on

- [Nisan–Szegedy: block sensitivity is at most quadratic in degree and approximate degree](nisan-szegedy-bounds.md)
- [Minsky–Papert symmetrization](minsky-papert-symmetrization.md)

## Sources

- N. Nisan and M. Szegedy, "On the Degree of Boolean Functions as Real Polynomials", Computational Complexity 4(4), 1994.
- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002.
