# Vanishing of ℓ∞-cohomology is undecidable for finitely presented groups and finite simplicial complexes

For every $n \ge 1$ there is no algorithm that decides whether the $\ell^\infty$-cohomology in degree $n$ with real coefficients vanishes, either for the group given by a finite presentation or for a given finite simplicial complex.

Let $X$ be a connected CW complex with fundamental group $G$, and let $V$ be a normed real vector space. Let $\ell^\infty(G, V)$ be the $\mathbb{R}[G]$-module of functions $G \to V$ with bounded image. The $\ell^\infty$-*cohomology* $H^\bullet_{(\infty)}(X; V)$ of $X$ is the cohomology of $X$ with coefficients in the local system $\ell^\infty(G, V)$; for a group $G$, $H^\bullet_{(\infty)}(G; V)$ is the group cohomology $H^\bullet(G; \ell^\infty(G, V))$. When $X$ has a finite $m$-skeleton, $H^k_{(\infty)}(X; V)$ for $k < m$ is the cohomology of the complex of cellular cochains on the universal cover of $X$ whose values are bounded, Gersten's original definition.

**Theorem (Milizia).** For every $n \ge 1$ the following algorithmic problems are undecidable:

1. given a finite presentation $\langle S \mid R \rangle$, decide whether $H^n_{(\infty)}(\langle S \mid R \rangle; \mathbb{R}) = 0$;
2. given a finite simplicial complex $X$, decide whether $H^n_{(\infty)}(X; \mathbb{R}) = 0$.

Conventions: a finite simplicial complex is described by its vertex set and the list of its simplices; the degree $n$ is fixed. The source proves finer statements for complexes of each fixed dimension. Gersten introduced $\ell^\infty$-cohomology to bound Dehn functions; for a finitely presented group, vanishing in degree $2$ for all normed coefficients characterizes hyperbolicity (Mineyev).

## Depends on

- [Integral singular homology](../../algebraic-topology/hurewicz-theorem/integral-homology.md)
- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Normed vector space](../../../Analysis/banach-spaces/normed-spaces/normed-space.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The key input is that a connected CW complex $X$ with finite $1$-skeleton and infinite fundamental group has $H^{n+1}_{(\infty)}((S^1)^n \times X; \mathbb{R}) \ne 0$ for every $n \ge 0$: in degree $1$, the distance from a base vertex in the universal cover is an unbounded $0$-cochain with bounded coboundary, which gives a nonzero class. For presentations, given a finite presentation of a group $H$ form $G = \mathbb{Z}^{n-1} \times H$. If $H$ is infinite, $H^n_{(\infty)}(G; \mathbb{R}) \ne 0$ by the nonvanishing result; if $H$ is finite, $G$ has a finite-index subgroup isomorphic to $\mathbb{Z}^{n-1}$, so it has the same $\ell^\infty$-cohomology, which vanishes in degree $n$ for dimensional reasons. Deciding vanishing would therefore decide finiteness of $H$, contradicting the Adian–Rabin theorem for the class of finite groups. The case of simplicial complexes is handled in the same way with explicit complexes. A good expansion links Proposition 7.1, the invariance of $\ell^\infty$-cohomology under passing to finite-index subgroups and the Adian–Rabin theorem for finiteness, which have no pages here.

## Sources

- Francesco Milizia, *$\ell^\infty$-cohomology: amenability, relative hyperbolicity, isoperimetric inequalities and undecidability*, J. Topol. Anal. 18 (2026), no. 6, 1645–1674 (online 2025), https://doi.org/10.1142/S1793525325500268, read in the copy arXiv:2107.09089v4: the statement is Theorem 1.6 there, the definitions are in its introduction, and the proof, with the nonvanishing result for infinite fundamental groups (Proposition 7.1), is in Section 7 ("Some undecidable algorithmic problems"), with the finer statements for complexes of fixed dimension in Theorem 7.3.
