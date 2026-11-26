# Outputs of polynomial-time functions have small K^t

Let $g$ be computable in polynomial time. Then there are a polynomial $q$ and a constant $c$ such that $K^{q}(g(z)) \le |z| + c$ for every input $z$, where the time bound is measured in $|g(z)|$ when $|g(z)| \ge |z|$. Consequently a pseudorandom generator $G : \{0,1\}^{\ell} \to \{0,1\}^n$ computable in polynomial time has outputs with $K^q \le \ell + c$, while most $n$-bit strings have $K^q \ge n - 1$.

## Proof sketch

The program consists of a fixed self-delimiting description of a machine for $g$ followed by $z$ verbatim; the universal machine simulates it with polynomial overhead.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](time-bounded-kolmogorov-complexity-and-levin-kt.md)
- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

- [Invariance theorem for time-bounded complexity](invariance-for-time-bounded-complexity.md)

## Sources

- Y. Liu and R. Pass, "On One-way Functions and Kolmogorov Complexity", FOCS 2020.
