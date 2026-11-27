# Goldreich-Levin: hardcore predicate from one-way permutations

Let $\pi$ be a family of
bijections $\pi_n$ of the set of $n$-bit strings, one for each natural number $n$. Suppose that
$\pi$ is computable by polynomial-size circuits: there is a polynomial $q$ with natural number
coefficients such that for every $n$ some list of at most $q(n)$ serialized gates has, on every
$n$-bit string $x$, outputs (its last $n$ gate values) equal to $\pi_n(x)$. Suppose also that $\pi$
is one-way: for every polynomial $p$ with natural number coefficients and every family $(C_n)$ of
lists of serialized gates with at most $p(n)$ gates in $C_n$ for all $n$, the inversion success
probability of $C_n$ against $\pi_n$ is a negligible function of $n$. Then for every polynomial
$p$ with natural number coefficients and every family $(C'_n)$ of lists of serialized gates with
at most $p(n)$ gates in $C'_n$ for all $n$, the function $n \mapsto \max(0, s_n - 1/2)$ is
negligible, where $s_n$ is the prediction success probability of $C'_n$ against $\pi_n$ for the
inner product modulo 2.

This statement is weaker than the theorem of the cited paper in one respect: it assumes that $\pi$
is a family of permutations of $\{0,1\}^n$, whereas Goldreich and Levin's theorem, as the title of
their paper says, applies to every one-way function $f$, the inner product $\langle x, r\rangle$
being hard-core for $(x, r) \mapsto (f(x), r)$. The permutation case is the one used to build
pseudorandom generators from one-way permutations; Arora and Barak state it with explicit
concrete-security bounds (an algorithm running in time $S(n) = \min(s(n), 1/\varepsilon(n))^{1/8}$
predicts $\langle x, r\rangle$ with probability at most $\tfrac12 + O(1/S(n))$, where $s$ and
$\varepsilon$ are the security and the success bound of the permutation).

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Internet draft dated January
  2007 (a pre-publication draft), Theorem 10.14 (the concrete-security form for one-way
  permutations).
- O. Goldreich and L. A. Levin, "A hard-core predicate for all one-way functions", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing (STOC 1989), 25-32.
