# Supports of extendible measures on 2×2 boxes are undecidable

No algorithm decides, given a finite set of colorings of a 2×2 box of ℤ², whether it is the support of a measure on such colorings that is the marginal of some translation-invariant measure on colorings of the whole plane.

**Setting (Goldstein, Kuna, Lebowitz and Speer).** Let $\Omega$ be a finite set, $X = \Omega^{\mathbb Z^2}$ the configurations of the plane, and for $\Lambda \subset \mathbb Z^2$ let $X_\Lambda = \Omega^\Lambda$. A [probability measure](../../../Probability/foundations/probability-measures/is-probability-measure.md) $\mu_\Lambda$ on $X_\Lambda$ is *extendible* if there is a probability measure $\mu$ on $X$, invariant under all translations of $\mathbb Z^2$, whose marginal on $X_\Lambda$ is $\mu_\Lambda$. It is *locally translation invariant* (LTI) if for all $A, A' \subseteq \Lambda$ with $A'$ a translate of $A$, the marginal of $\mu_\Lambda$ on $X_{A'}$ is the translate of its marginal on $X_A$; this is necessary for extendibility. Fix $\Lambda$ to be a $2 \times 2$ box. A finite set $Y \subseteq X_\Lambda$ (for some finite $\Omega$) is a set of *tiles*, and $Y$ *tiles the plane* if some configuration in $X$ has its restriction to every $2 \times 2$ box in $Y$.

**Theorem (Goldstein, Kuna, Lebowitz and Speer).** There is no algorithm that, given a set of tiles $Y \subseteq X_\Lambda$, decides whether there exists an extendible measure on $X_\Lambda$ with support $Y$. Equivalently, there is no algorithm that, given an LTI measure $\mu_\Lambda$ on $X_\Lambda$, decides whether some extendible measure on $X_\Lambda$ has the same support as $\mu_\Lambda$ (Corollary 21 of the source).

The input is a finite set of tiles, not a measure: as the source notes, most measures $\mu_\Lambda$ are not computable and so cannot be given to an algorithm, and whether a given LTI measure is itself extendible is left without a precise undecidability statement. For $\Lambda$ an interval of $\mathbb Z$ the LTI condition is necessary and sufficient for extendibility, while for $\Lambda \subset \mathbb Z^d$ with $d \ge 2$ it is necessary but not sufficient.

## Depends on

- [Probability measure](../../../Probability/foundations/probability-measures/is-probability-measure.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof combines two results. First, Berger's theorem that the tiling problem is undecidable, stated for Wang tiles, implies the same for sets of $2 \times 2$ tiles in the sense above (an observation of Schlijper, not detailed in the source). Second, Schlijper's theorem: a set of tiles $Y$ tiles the plane if and only if there exists an extendible measure on $X_\Lambda$ with support $Y$. Neither the translation from Wang tiles to $2 \times 2$ tiles nor Schlijper's theorem has a page here.

## Sources

- S. Goldstein, T. Kuna, J. L. Lebowitz and E. R. Speer, "Translation invariant extensions of finite volume measures", *Journal of Statistical Physics* 166(3–4), 2017, pp. 765–782, doi:[10.1007/s10955-016-1595-8](https://doi.org/10.1007/s10955-016-1595-8), with an erratum in *Journal of Statistical Physics* 166(3–4), 2017, p. 783, doi:[10.1007/s10955-016-1711-9](https://doi.org/10.1007/s10955-016-1711-9) (the erratum was not read); read as arXiv:1508.04448v2, <https://arxiv.org/abs/1508.04448v2>, whose numbering is used: the definitions of extendibility and local translation invariance in Section 1, Theorem 18 (tiling problem), Theorem 20 (Schlijper) and Corollary 21 in Section 7 ("Undecidability").
