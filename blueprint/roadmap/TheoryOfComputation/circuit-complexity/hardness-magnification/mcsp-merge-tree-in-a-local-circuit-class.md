# The McKay–Murray–Williams merge tree is a local circuit

Unconditionally, for every constructive $s(n) \le 2^n / \mathrm{poly}(n)$ at input length $N = 2^n$, $\mathrm{MCSP}[s]$ is computed by oracle circuits with one fixed oracle for all lengths, $O(N / \mathrm{poly}(s))$ oracle gates each of fan-in $\mathrm{poly}(s)$, at most $O(n / \log s)$ oracle gates on any path, and $N / \mathrm{poly}(s)$ gates in total: in the notation of local classes, $\mathrm{MCSP}[s] \in [O(N / \mathrm{poly}(s)), \mathrm{poly}(s), O(n / \log s)]\text{-}\mathrm{Circuit}[N / \mathrm{poly}(s)]$ (Chen et al. 2020, building on McKay, Murray and Williams 2019).

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
