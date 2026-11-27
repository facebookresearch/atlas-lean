# Distinct rows and the rank upper bound on communication

Let $K$ be a field and $M$ a $0/1$ matrix over $K$ of rank $r$. Then $M$ has at most $2^r$ distinct rows. Consequently, for every Boolean $f$ on finite input sets, $D(f) \le \mathrm{rank}_K(M_f) + 1$. If the rows of $M_f$ are pairwise distinct on $n$-element row sets, then $\mathrm{rank}_K(M_f) \ge \log_2 n$, every **one-way** protocol in which Alice sends a single message and Bob announces the answer needs a message of at least $\lceil \log_2 n \rceil$ bits, and for $n \ge 2$ every (interactive) protocol has $D(f) \ge \lceil \log_2 \log_2 n \rceil$ by the log-rank bound.

The distinct-row count does not lower-bound two-way communication by $\log_2 n$: if Alice holds four bits and Bob an index in $[4]$, and the output is Alice's indexed bit, there are $16$ distinct rows, but Bob sends his index in two bits and Alice announces the bit, so $D \le 3 < 4$.

## Proof sketch

Choose $r$ linearly independent columns; every row is determined by its entries in these columns, which take at most $2^r$ patterns. Alice sends the index of her row's pattern in $r$ bits and Bob announces the answer. In a one-way protocol, two distinct rows sent the same message would get the same answers from Bob in every column, although they differ in some column.

## Depends on

- [Communication matrix](../deterministic-communication-protocols/comm-matrix.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Proof depends on

- [Log-rank lower bound](../deterministic-communication-protocols/log-rank-le-comm-complexity.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
