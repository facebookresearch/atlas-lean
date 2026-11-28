# The aperiodic domino problem for sofic subshifts is Σ¹₁-complete in dimension at least 3

For every $d \ge 3$, deciding whether a given sofic subshift of $\Sigma^{\mathbb{Z}^d}$ contains an aperiodic configuration is $\Sigma^1_1$-complete; the problem lies outside the arithmetical hierarchy and is in particular undecidable.

**Theorem.** Let $d \ge 3$. The [aperiodic domino problem](aperiodic-domino-problem.md) for $\mathbb{Z}^d$ sofic subshifts, whose input is an SFT $X$ given by a finite family of forbidden patterns together with a letter-to-letter map $\pi$ and whose question is whether $\pi(X)$ contains a configuration with no nonzero period, is [$\Sigma^1_1$-complete](../../../degrees-and-hierarchies/analytical-class-sigma-1-1.md) under many-one reductions.

In dimension $2$ the problem is $\Pi^0_1$-complete for SFTs, sofic and effective subshifts alike, so the complexity jumps between dimensions $2$ and $3$; for SFTs, $\Sigma^1_1$-completeness is known from dimension $4$ (see [the SFT case](aperiodic-domino-problem-for-sfts.md)), and the three-dimensional SFT case is open; the source conjectures it to be arithmetical.

## Depends on

- [The aperiodic domino problem](aperiodic-domino-problem.md)
- [Subshifts of finite type, sofic and effective subshifts](subshifts-and-the-aperiodic-domino-problem.md)
- [The analytical class Σ¹₁ and Σ¹₁-hardness under many-one reductions](../../../degrees-and-hierarchies/analytical-class-sigma-1-1.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Membership in $\Sigma^1_1$ holds for every $d$ (Proposition 10 of the source). For hardness in dimension $3$, the proof reduces *State Recurrence*: given a nondeterministic Turing machine $\mathcal{M}$ and a state $q_0$, is there a run of $\mathcal{M}$ on the empty input that visits $q_0$ infinitely often? This problem is $\Sigma^1_1$-complete (Harel). From $(\mathcal{M}, q_0)$ one first encodes the state sequences of the runs of $\mathcal{M}$ in a one-dimensional Toeplitz subshift $T_{\mathcal{M}}$, which is effective because the prefixes of these sequences are computable. Two-dimensional subshifts built from it are effective, and by the theorem of Durand, Romashchenko and Shen and of Aubrun and Sablik their lifts to one more dimension are sofic; combining them gives a sofic subshift $Y_3 \subseteq \Sigma^{\mathbb{Z}^3}$ in which one direction is always aperiodic and the two others may or may not be periodic, and the Toeplitz structure lets every period be broken exactly when the encoded run visits $q_0$ infinitely often. So $Y_3$ contains an aperiodic configuration if and only if $(\mathcal{M}, q_0)$ is a positive instance of State Recurrence. For $d > 3$, the product of the $\mathbb{Z}^d$ lift of $Y_3$ with the lift of an aperiodic $\mathbb{Z}^{d-2}$ sofic subshift is aperiodic exactly when $Y_3$ is.

## Sources

- A. Callard and B. Hellouin de Menibus, "The Aperiodic Domino Problem in Higher Dimension", *39th International Symposium on Theoretical Aspects of Computer Science (STACS 2022)*, Leibniz International Proceedings in Informatics 219, 2022, Article 19, doi:[10.4230/LIPIcs.STACS.2022.19](https://doi.org/10.4230/LIPIcs.STACS.2022.19); numbering of arXiv:2202.07377v1: Theorem 11 with its proof in Section 3, Theorem 7 (State Recurrence, quoted from Harel), Theorem 4 (lifts of effective subshifts are sofic) and the summary table in Section 1.
