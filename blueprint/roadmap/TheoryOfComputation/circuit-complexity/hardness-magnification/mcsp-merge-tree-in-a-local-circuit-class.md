# The McKay–Murray–Williams merge tree is a local circuit

Unconditionally, whenever $n \le s(n)$ and $2 \le s(n)$, $\mathrm{MCSP}[s]$ on input length $N = 2^n$ is computed by oracle circuits, with one fixed oracle for all lengths, having at most $128 N / s(n) + 1$ oracle gates, each of fan-in at most $12\, s(n)^4$, at most $n / \lfloor \log_2 s(n) \rfloor + 1$ oracle gates on any path, and at most $129 N/s(n) + 3$ gates in total. In the notation of local classes this is $[O(N/s), O(s^4), O(n/\log s)]\text{-}\mathrm{Circuit}[O(N/s)]$.

## Proof sketch

Use a merge tree in which each node merges $2^{\lfloor \log_2 s\rfloor}$ children at once; each merge is one oracle gate whose query consists of the children's certificates (lists of small circuits, of length $O(s^4)$ bits in total), and the tree has depth $n/\lfloor\log_2 s\rfloor$.

## Depends on

- [Oracle circuits and local circuit classes](oracle-circuits-and-local-circuit-classes.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../minimum-circuit-size-problem/minimum-circuit-size-problem.md)

## Proof depends on

- [McKay–Murray–Williams: under NP ⊆ P/poly, MCSP[s] has circuits of size 2^n·poly(n + s)](mckay-murray-williams-merge-circuits.md)

## Sources

- L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal and R. Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", ITCS 2020.
- D. McKay, C. D. Murray and R. R. Williams, "Weak Lower Bounds on Resource-Bounded Compression Imply Strong Separations of Complexity Classes", STOC 2019.
