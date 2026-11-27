# Hirahara–Nanashima: O(log n) knowledge complexity for GapMCSP suffices to characterize one-way functions by worst-case hardness of CZK

For every constant $\epsilon\in(0,1/2)$, with $\mathrm{Gap}_\epsilon\mathrm{MCSP}$ the problem of distinguishing truth tables of $f:\{0,1\}^n\to\{0,1\}$ of circuit complexity at most $2^{\epsilon n}$ from those of circuit complexity at least $2^{(1-\epsilon)n}$, the following are equivalent:

1. There is a one-way function secure against $\mathsf{P/poly}$.
2. $\mathsf{NP}\not\subseteq\mathsf{i.o.P/poly}$ and $\mathsf{NP}$ has an interactive proof system of computational knowledge complexity $O(\log n)$ with negligible soundness error.
3. $\mathsf{CZK}\not\subseteq\mathsf{i.o.P/poly}$ and $\mathrm{Gap}_\epsilon\mathrm{MCSP}$ has interactive proof systems of computational knowledge complexity $O(\log n)$ with negligible soundness error.

Complementing this (using the almost-everywhere-in-length auxiliary-input one-way function definition, Definition 4.6, Theorems 2.4–2.5): if an auxiliary-input one-way function secure against $\mathsf{P/poly}$ exists, then for every constant $\epsilon>0$ every language in $\mathsf{NP}$ has an interactive proof of computational knowledge complexity $n^{\epsilon}$ with negligible completeness and soundness errors; and if for some constant $\delta>0$ an auxiliary-input one-way function exponentially secure against $\mathrm{SIZE}[2^{\delta n}]$ exists, then for every increasing $k(n)=\omega(\log n)$, $\mathsf{NP}$ has interactive proofs of computational knowledge complexity $k(n)$.

## Proof sketch

The $O(\log n)$ leakage can be absorbed by guessing the $k(n)=O(\log n)$ advice bits: a simulator that enumerates all $2^{k(n)}=\mathrm{poly}(n)$ advice strings loses only a polynomial factor in the distinguishing advantage, so the argument for zero knowledge goes through with polynomial loss. For the complementary results, an auxiliary-input one-way function is used in the GMW commitment-based proof for $\mathsf{NP}$, with the leaked bits identifying a hard auxiliary input $z$ of bit length $n^{\epsilon}$ (or $k(n)$ under exponential security) so that the commitments are hiding.

## Depends on

- [Computational knowledge complexity k(n) of an interactive proof](computational-knowledge-complexity.md)
- [Auxiliary-input one-way functions](auxiliary-input-one-way-functions.md)
- [GapMCSP[s,c], GapK[s,c] and weak versus strong average-case hardness on a distribution](gap-meta-complexity-and-weak-strong-average-case-hardness.md)
- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)
- [Zero-knowledge interactive proofs](../../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)

## Proof depends on

- [Hirahara–Nanashima: one-way functions exist iff NP ⊆ CZK and NP is worst-case hard (converse of Goldreich–Micali–Wigderson)](hirahara-nanashima-owf-iff-np-in-czk.md)

## Sources

- Shuichi Hirahara and Mikito Nanashima, "One-Way Functions and Zero Knowledge", STOC (2024), ECCC TR24-063.
