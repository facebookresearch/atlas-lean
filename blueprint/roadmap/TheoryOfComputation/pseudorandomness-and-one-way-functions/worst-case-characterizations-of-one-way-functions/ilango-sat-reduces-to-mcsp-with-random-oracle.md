# Ilango: with probability 1 over a random oracle O, approximate hypergraph vertex cover reduces to MCSP^O, so NP ⊆ P^{MCSP^O}/poly

Let $O$ be a uniformly random oracle ($O(z)$ an independent uniform bit for every $z$) and let $\mathrm{MCSP}^{O}$ be MCSP for circuits with $O$-oracle gates. With probability $1$ over $O$:

1. there is a $\mathsf{P/poly}$ many-one reduction from the $\mathsf{NP}$-hard problem of approximating vertex cover on $\tau$-uniform hypergraphs (constant $\tau$; reformulated as Gap $\tau$-Frequency Set Cover) to $\mathrm{MCSP}^{O}$, and the same reduction with a different size threshold reduces it to computing $K^{t}$ relative to $O$;
2. consequently $\mathsf{NP}\subseteq\mathsf{P}^{\mathrm{MCSP}^{O}}/\mathrm{poly}$;
3. given oracle access to $O$, the reduction can be made uniform deterministic polynomial-time, and it achieves additive hardness of approximation optimal up to a constant factor.

This confirms a conjecture of Huang, Ilango and Ren. Instantiating $O$ heuristically with cryptographic hash functions yields candidate uniform deterministic polynomial-time reductions from SAT to MCSP and to $K^t$; and since approximate $K^t$ has a non-black-box worst-case to average-case reduction (Hirahara), sufficiently unstructured functions would make a problem with such a reduction $\mathsf{NP}$-complete.

## Proof sketch

The reduction uses parameter $\lambda=\Theta(\log n)$ and oracles $O_n:[n]\times\{0,1\}^{\lambda}\times\{0,1\}^{2\lambda}\to\{0,1\}^{\lambda}$; the truth table is built from oracle answers indexed by the sets of the cover instance, and a key ingredient is that computing it requires a cryptographic proof of work relative to $O$ unless one knows a small cover. Completeness gives a small circuit from a small cover; soundness rests on a pseudo symmetry of information principle for random oracles, a weak form of time-bounded SoI that holds unconditionally relative to $O$ and shows that any small circuit for the truth table must essentially reveal a small cover.

## Depends on

- [The random oracle model](../../../ComputerScience/cryptography/public-key/random-oracle-constructions/the-random-oracle-model.md)
- [GapMCSP[s,c], GapK[s,c] and weak versus strong average-case hardness on a distribution](gap-meta-complexity-and-weak-strong-average-case-hardness.md)
- [Kolmogorov complexity](../../kolmogorov-complexity/k.md)

## Sources

- Rahul Ilango, "SAT Reduces to the Minimum Circuit Size Problem with a Random Oracle", FOCS (2023), ECCC TR23-165.
