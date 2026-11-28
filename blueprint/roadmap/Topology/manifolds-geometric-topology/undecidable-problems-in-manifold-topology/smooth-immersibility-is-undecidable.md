# Smooth immersibility of manifolds in Euclidean space is undecidable in a range of even codimension

Let $n \ge 4$ and $m < n$ with $n - m$ even and $5m \ge 4n$. There is no algorithm that decides whether a given smooth $m$-manifold immerses in $\mathbb{R}^n$, even when only closed manifolds are allowed as inputs.

As in Section 2.2.1 of the source, a compact smooth $m$-manifold is given by a $C^1$ triangulation: a finite simplicial complex together with, for each top-dimensional simplex, a polynomial map with rational coefficients to some $\mathbb{R}^N$, such that the derivatives are nonsingular and the maps on adjacent simplices patch together to a $C^1$ immersion; whether such data defines a closed manifold, or a manifold with boundary, can be decided from it. An *immersion* of a smooth manifold $M$ in $\mathbb{R}^n$ is a smooth map whose differential is injective at every point.

**Theorem (Manin–Weinberger).** Let $n \ge 4$ and $m < n$ be natural numbers.

1. If $n - m$ is even and $5m \ge 4n$, then there is no algorithm that decides whether a given smooth $m$-manifold immerses in $\mathbb{R}^n$; this remains true when only closed manifolds are considered.
2. If $n - m = 2$ and $n \ge 10$, then there is no algorithm that decides whether a given PL $m$-manifold has a locally flat PL immersion in $\mathbb{R}^n$.

Conventions: the dimensions $m$ and $n$ are fixed and the manifold is the input. The same theorem of the source states decidability in the complementary cases it settles: smooth immersibility is decidable when $n - m$ is odd or $3m \le 2n - 1$, PL immersibility when $n - m \ne 2$, and not necessarily locally flat PL immersibility when $n - m = 2$; some pairs with $n - m$ even remain open.

## Depends on

- [Closed manifold, not required to be connected](../closed-topological-manifold.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

By the Smale–Hirsch theorem (and Haefliger–Poenaru in the PL case), immersions of $M$ in $\mathbb{R}^n$ correspond up to homotopy to lifts of the classifying map of the tangent bundle of $M$ to a suitable Grassmannian, so immersibility becomes a homotopy-theoretic lifting problem. In the smooth case this lifting property is stable, so for $m < n$ and $M$ oriented it reduces to lifting the stable tangent classifying map $M \to BSO$ through $BSO_{n-m} \to BSO$; the proof of the source treats the oriented case first, to avoid fundamental group issues. Following the work of Čadek, Krčál, Matoušek, Vokřínek and Wagner on extension problems, where deciding which rational homotopy invariants can be attained amounts to solving systems of Diophantine equations, Manin and Weinberger show that in the stated range the lifting problem reduces from Hilbert's tenth problem, which gives undecidability of immersibility. A good expansion links the Smale–Hirsch and Haefliger–Poenaru theorems and this reduction of the lifting problem to Diophantine equations.

## Sources

- Fedor Manin and Shmuel Weinberger, *Algorithmic aspects of immersibility and embeddability*, Int. Math. Res. Not. IMRN 2024, no. 17, 12433–12454, https://doi.org/10.1093/imrn/rnae170, read in the copy arXiv:1812.09413v4, whose numbering is used here: the input model is Section 2.2.1; the statement is Theorem 3.1 at the start of Section 3 ("Immersibility"), clauses (ii) and (iv), with the decidable clauses (i) and (iii) and the reduction to lifting problems in its proof; the theorem is also quoted in Section 1.2.
