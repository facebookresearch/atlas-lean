# Probabilistic-method explicit constructions reduce to Avoid

Each of the following explicit construction problems, with parameters matching those guaranteed by the probabilistic method, lies in $\mathrm{APEPP}$, that is, reduces in polynomial time to Avoid: truth tables of length $2^n$ and circuit complexity $2^n/(2n)$; pseudorandom generators against circuits of fixed polynomial size; $n\times n$ matrices over $\mathbb{F}_2$ of high rigidity; Ramsey graphs; two-source extractors; binary linear codes on the Gilbert–Varshamov bound; strings of maximum $\mathrm{K}^{\mathrm{poly}}$ (time-bounded Kolmogorov) complexity.

For several of them (for instance rigid matrices) there are direct polynomial-time reductions to constructing hard truth tables; e.g. if $\mathrm{E}$ contains a language of circuit complexity $\Omega(2^n/n)$ then there are constants $c,d>0$ such that an $n\times n$ matrix over $\mathbb{F}_2$ differing in at least $dn^2$ entries from every matrix of rank at most $cn$ is constructible in polynomial time (Korten, Theorem 12).

## Proof sketch

In each case the bad objects admit short descriptions: a non-rigid matrix is a low-rank matrix plus a sparse matrix, a non-Ramsey graph is determined by a planted clique or independent set plus the remaining edges, a bad code by a low-weight codeword, a compressible string by its short program. The circuit mapping descriptions to objects has stretch, so any non-image is a good object.

## Depends on

- [The total function class TFΣ2P and the explicit-construction class APEPP](tfsigma2p-and-apepp.md)
- [Gilbert–Varshamov bound for linear codes](../../../../InformationTheory/error-correcting-codes/bounds-on-code-size/exists-linear-code-finrank-eq.md)
- [Pseudorandom generators against circuits](../../../pseudorandomness-and-one-way-functions/derandomization/pseudorandom-generators-against-circuits.md)
- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)

## Sources

- Oliver Korten, "The Hardest Explicit Construction", FOCS (2021), arXiv:2106.00875.
- Zeyong Li, "Symmetric Exponential Time Requires Near-Maximum Circuit Size: Simplified, Truly Uniform", STOC (2024), arXiv:2310.17762.
