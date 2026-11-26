# Yannakakis: clique versus independent set in O(log² n) bits

Let $H$ be a simple graph on $n$ vertices. If Alice holds a clique $C$ and Bob an independent set $I$ of $H$, they can compute $|C \cap I| \in \{0, 1\}$ with a deterministic protocol of depth at most $3(\lfloor \log_2 n \rfloor + 1)^2$, uniformly in $H$.

## Proof sketch

In each round, if $C$ contains a vertex of degree less than half of the remaining graph, Alice names it (and Bob checks membership or restricts to its neighbourhood); otherwise if $I$ contains a vertex of degree at least half, Bob names it; otherwise they conclude $C \cap I = \emptyset$. Each round halves the remaining vertex set and costs $O(\log n)$ bits.

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
