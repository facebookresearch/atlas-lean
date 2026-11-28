# The aperiodic domino problem for subshifts of finite type is Σ¹₁-complete in dimension at least 4

For every $d \ge 4$, deciding whether the subshift of $\Sigma^{\mathbb{Z}^d}$ defined by a given finite set of forbidden patterns contains an aperiodic configuration is $\Sigma^1_1$-complete; the problem lies outside the arithmetical hierarchy and is in particular undecidable.

**Theorem.** Let $d \ge 4$. The [aperiodic domino problem](aperiodic-domino-problem.md) for $\mathbb{Z}^d$ subshifts of finite type, whose input is a finite family $\mathcal{F}$ of $d$-dimensional patterns and whose question is whether $X_{\mathcal{F}}$ contains a configuration with no nonzero period, is [$\Sigma^1_1$-complete](analytical-class-sigma-1-1.md) under many-one reductions.

The three-dimensional case for SFTs is open in the source, which conjectures that it lies in the arithmetical hierarchy; in dimension $2$ the problem is $\Pi^0_1$-complete.

## Depends on

- [The aperiodic domino problem](aperiodic-domino-problem.md)
- [Subshifts of finite type, sofic and effective subshifts](subshifts-and-the-aperiodic-domino-problem.md)
- [The analytical class Σ¹₁](analytical-class-sigma-1-1.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Membership in $\Sigma^1_1$ holds for every $d$ (Proposition 10 of the source). Hardness is proved for $d = 4$ by a reduction from State Recurrence, the $\Sigma^1_1$-complete problem asking whether a nondeterministic Turing machine has a run on the empty input visiting a given state infinitely often (Harel): following the sofic construction, an SFT $X_4$ is built that contains an aperiodic configuration if and only if the machine has such a run, using lines repeated along dimensions $3$ and $4$ to break all periods up to a length controlled by an embedded computation (bi-Toeplitz layers replace the sofic Toeplitz layers). The cases $d > 4$ follow by the same lifting argument as for sofic subshifts.

## Sources

- A. Callard and B. Hellouin de Menibus, "The Aperiodic Domino Problem in Higher Dimension", *39th International Symposium on Theoretical Aspects of Computer Science (STACS 2022)*, Leibniz International Proceedings in Informatics 219, 2022, Article 19, doi:[10.4230/LIPIcs.STACS.2022.19](https://doi.org/10.4230/LIPIcs.STACS.2022.19); numbering of arXiv:2202.07377v1: Theorem 17 with its proof in Section 4, Theorem 7 (State Recurrence) and the summary table and conjecture in Sections 1 and 6.
