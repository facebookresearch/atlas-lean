# Randomized protocol for greater-than with logarithmic cost

For integers $a, b \in \{0, 1, \dots, 2^{n} - 1\}$ held by Alice and Bob, there is a public-coin randomized protocol deciding whether $a \ge b$ with error at most $\varepsilon$ and communication $O(\log n + \log(1/\varepsilon))$ (Nisan, §3.1, Theorem 1a); in particular, for error $1/\operatorname{poly}(n)$ this gives $O(\log n)$ communication. Deterministically, greater-than requires $n + 1$ bits.

## Proof sketch

Binary search for the most significant bit where $a$ and $b$ differ, testing equality of prefixes with public-coin hashing; each equality test errs with small probability, and a noisy binary search with backtracking keeps the total number of steps at $O(\log n)$. The deterministic lower bound follows since the communication matrix is triangular with full rank.

## Depends on

- [Public-coin randomized protocol](../randomized-communication-protocols/public-coin-protocol.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Sources

- N. Nisan, "The communication complexity of threshold gates", Combinatorics, Paul Erdős is Eighty, Vol. 1 (1993) 301-315.
- E. Kushilevitz, N. Nisan, "Communication Complexity", Cambridge University Press (1997).
