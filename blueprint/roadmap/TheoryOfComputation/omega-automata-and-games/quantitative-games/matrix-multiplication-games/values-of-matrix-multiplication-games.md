# The value of matrix multiplication games is not computable

For determined matrix multiplication games with finite sets of integer matrices, the value is not computable from the matrices, even under the promise that it is $0$ or $1$.

**Theorem.** There is no algorithm that, given finite sets $\mathcal{A}, \mathcal{E}$ of matrices with integer entries such that the [matrix multiplication game](matrix-multiplication-games.md) on $(\mathcal{A}, \mathcal{E})$ is determined with value $V \in \{0, 1\}$, decides whether $V = 0$ (Lemma 3 and Theorem 5 of the source). In particular no algorithm computes the value $V$ of determined games on finite sets of integer matrices.

Hence the value cannot be approximated either, and it is not computable as a function of the matrices in the sense of computable analysis. Already with Adam trivial, deciding $V \le \alpha$ for given finite sets of non-negative rational matrices and $\alpha \in \mathbb{Q}_+$ is undecidable, because the value is then the joint spectral radius of Eve's set, and deciding whether the joint spectral radius is at most $1$ is undecidable (Blondel and Tsitsiklis); the source describes the decidability of whether it is below $1$ as unknown.

## Depends on

- [Matrix multiplication games](matrix-multiplication-games.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

From a two-counter machine $M$ one builds finite sets $\mathcal{A}, \mathcal{E}$ of integer square matrices of dimension $|Q| + 5$, where $Q$ is the state set of $M$: coordinates hold the current state, the two counters and auxiliary values, and Eve's matrices increment, decrement or keep a counter and change state. Eve tries to simulate $M$ from zero counters; Adam can play the identity or matrices that detect a cheat, such as a zero-test transition applied to a positive counter, and then reset the product. If $M$ does not halt, the game is determined with value $1$; if $M$ halts, it is determined with value $0$ (Lemma 3 of the source). Computing $V$, even knowing $V \in \{0, 1\}$, would therefore decide the halting problem for two-counter machines.

## Sources

- E. Asarin, J. Cervelle, A. Degorre, C. Dima, F. Horn and V. Kozyakin, "Entropy Games and Matrix Multiplication Games", *33rd Symposium on Theoretical Aspects of Computer Science (STACS 2016)*, Leibniz International Proceedings in Informatics 47, 2016, Article 11, doi:[10.4230/LIPIcs.STACS.2016.11](https://doi.org/10.4230/LIPIcs.STACS.2016.11); numbering of arXiv:1506.04885v3: Theorem 5 with Lemma 3 (simulation of two-counter machines by integer matrices) and its proof sketches in the appendix, and Theorem 2 (the joint spectral radius case) in Section 3.
