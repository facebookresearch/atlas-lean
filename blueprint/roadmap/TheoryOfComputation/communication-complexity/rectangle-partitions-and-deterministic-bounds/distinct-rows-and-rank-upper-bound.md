# Distinct rows and the rank upper bound on communication

Let $K$ be a field and $M$ a $0/1$ matrix over $K$ of rank $r$. Then $M$ has at most $2^r$ distinct rows. Consequently, for every Boolean $f$ on finite input sets, $D(f) \le \mathrm{rank}_K(M_f) + 1$, and if the rows of $M_f$ are pairwise distinct on $n$-element row sets then $\mathrm{rank}_K(M_f) \ge \log_2 n$ and $D(f) \ge \lceil \log_2 n \rceil$.

## Proof sketch

Choose $r$ linearly independent columns; every row is determined by its entries in these columns, which take at most $2^r$ patterns. Alice sends the index of her row's pattern in $r$ bits and Bob announces the answer.

## Depends on

- [Communication matrix](../deterministic-communication-protocols/comm-matrix.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Proof depends on

- [Log-rank lower bound](../deterministic-communication-protocols/log-rank-le-comm-complexity.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
