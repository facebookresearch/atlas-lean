# Nondeterministic complexity of equality, disjointness and inner product

For $n$-bit strings: $N^1(\mathrm{EQ}_n) = n$ and $N^0(\mathrm{EQ}_n) \le \lceil\log_2 n\rceil + 1$; $N^1(\mathrm{DISJ}_n) = n$ and $N^0(\mathrm{DISJ}_n) \le \lceil \log_2 n \rceil$ (equivalently $N^0$ of intersection is $n$); for the inner product modulo two, $N^1(\mathrm{IP}_n) \ge n - 1$ and $N^0(\mathrm{IP}_n) \ge n$. So nondeterminism helps exponentially for one answer of equality and disjointness but not for inner product.

## Proof sketch

Lower bounds come from fooling sets of size $2^n$ (diagonal pairs for equality, complementary pairs for disjointness) and, for inner product, from the fact that a monochromatic rectangle of $\mathrm{IP}_n$ has at most $2^n$ (resp. $2^{n+1}$) entries. Upper bounds guess a position where the inputs differ, or a common element.

## Depends on

- [Rectangle covers and nondeterministic communication complexity](rectangle-covers-and-nondeterministic-complexity.md)
- [Equality function](../deterministic-communication-protocols/eq-fn.md)
- [Set intersection function](../randomized-communication-protocols/disj-fn.md)

## Sources

- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
