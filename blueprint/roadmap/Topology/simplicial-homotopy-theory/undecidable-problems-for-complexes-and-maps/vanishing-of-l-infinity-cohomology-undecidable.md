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

The key input is that a connected CW complex $X$ with finite $1$-skeleton and infinite fundamental group has $H^{n+1}_{(\infty)}((S^1)^n \times X; \mathbb{R}) \ne 0$ for every $n \ge 0$: in degree $1$, the distance from a base vertex in the universal cover is an unbounded $0$-cochain with bounded coboundary, which gives a nonzero class. For clause 1 (Theorem 7.2), given a finite presentation of a group $H$ form $G = \mathbb{Z}^{n-1} \times H$. If $H$ is infinite, $H^n_{(\infty)}(G; \mathbb{R}) \ne 0$ by the nonvanishing result applied to a cellular $K(H, 1)$ with finite $1$-skeleton; if $H$ is finite, $G$ has a finite-index subgroup isomorphic to $\mathbb{Z}^{n-1}$, so it has the same $\ell^\infty$-cohomology (Remark 2.8), which vanishes in degree $n$ for dimensional reasons. Deciding vanishing would therefore decide finiteness of $H$, contradicting the Adian–Rabin theorem for the class of finite groups. Clause 2 needs a different input, a sequence of complexes rather than of presentations. It follows from Theorem 7.3 with $m = n + 1$: by Novikov's results (Section 10 of the survey of Volodin, Kuznetsov and Fomenko), for every $d \ge 6$ there is an effective sequence of finite $d$-dimensional simplicial complexes $Y_i$, each either contractible or with infinite fundamental group, such that no algorithm decides, given $i$, which case holds. Take $d \ge \max\{6, m - n + 1\}$ and let $X_i$ be the $m$-skeleton of a triangulation of $(S^1)^{n-1} \times Y_i$. Since $n < m$, $H^n_{(\infty)}(X_i; \mathbb{R}) \cong H^n_{(\infty)}((S^1)^{n-1} \times Y_i; \mathbb{R})$, which by Proposition 7.1 is nonzero exactly when $\pi_1(Y_i)$ is infinite, that is, exactly when $Y_i$ is not contractible. A good expansion links Proposition 7.1, the invariance of $\ell^\infty$-cohomology under passing to finite-index subgroups, the Adian–Rabin theorem for finiteness, and Novikov's sequence of complexes $Y_i$.

## Sources

- Francesco Milizia, *$\ell^\infty$-cohomology: amenability, relative hyperbolicity, isoperimetric inequalities and undecidability*, J. Topol. Anal. 18 (2026), no. 6, 1645–1674 (online 2025), https://doi.org/10.1142/S1793525325500268, read in the copy arXiv:2107.09089v4: the statement is Theorem 1.6 there, the definitions are in its introduction, and the proof, with the nonvanishing result for infinite fundamental groups (Proposition 7.1), is in Section 7 ("Some undecidable algorithmic problems"), with the finer statements for complexes of fixed dimension in Theorem 7.3, whose proof uses Novikov's sequence of complexes from Section 10 of the survey of Volodin, Kuznetsov and Fomenko.
- I. A. Volodin, V. E. Kuznetsov and A. T. Fomenko, *The problem of discriminating algorithmically the standard three-dimensional sphere*, Russian Math. Surveys 29 (1974), no. 5, 71–172, https://doi.org/10.1070/RM1974v029n05ABEH001296, whose Section 10 gives Novikov's sequence of complexes used for clause 2; cited beside the copy read above.
