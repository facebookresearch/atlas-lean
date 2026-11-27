# Yannakakis: clique versus independent set in O(log² n) bits

Let $H$ be a simple graph on $n \ge 1$ vertices. If Alice holds a clique $C$ and Bob an independent set $I$ of $H$, they can compute $|C \cap I| \in \{0, 1\}$ with a deterministic protocol of depth at most $3(\lfloor \log_2 n \rfloor + 1)^2$, uniformly in $H$.

## Proof sketch

In each round, if $C$ contains a vertex of degree less than half of the remaining graph, Alice names it (and Bob checks membership or restricts to its neighbourhood); otherwise if $I$ contains a vertex of degree at least half, Bob names it; otherwise they conclude $C \cap I = \emptyset$. A continuing round shrinks the remaining vertex set from $k$ to fewer than $k/2$ vertices and costs at most $\lceil \log_2 k \rceil + 3$ bits (a flag and a name from one player, a membership bit from the other, possibly after the first player's one-bit refusal); a stopping round costs at most $2$ bits. With at most $\lfloor \log_2 n \rfloor + 1$ continuing rounds the total is at most $(\lfloor \log_2 n \rfloor + 1)(\lceil \log_2 n \rceil + 3) + 2 \le 3(\lfloor \log_2 n \rfloor + 1)^2$ for $n \ge 2$, and at most $3$ for $n = 1$.

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
