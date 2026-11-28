# Smooth embeddability of manifolds with boundary in Euclidean space is undecidable in a range of even codimension

Let $n - m$ be even with $11m \ge 10n + 1$. There is no algorithm that decides whether a given smooth $m$-manifold with boundary embeds smoothly in $\mathbb{R}^n$.

As in Section 2.2.1 of the source, a compact smooth $m$-manifold is given by a $C^1$ triangulation: a finite simplicial complex together with, for each top-dimensional simplex, a polynomial map with rational coefficients to some $\mathbb{R}^N$, such that the derivatives are nonsingular and the maps on adjacent simplices patch together to a $C^1$ immersion; whether such data defines a closed manifold, or a manifold with boundary, can be decided from it. A smooth *embedding* of $M$ in $\mathbb{R}^n$ is an immersion that is a homeomorphism onto its image.

**Theorem (Manin–Weinberger).** Let $m < n$ be natural numbers with $n - m$ even and $11m \ge 10n + 1$. Then there is no algorithm that decides, for a given smooth $m$-manifold $M$ with boundary, whether $M$ embeds smoothly in $\mathbb{R}^n$.

Conventions: the dimensions are fixed and the manifold is the input; manifolds with nonempty boundary are allowed, and the source notes that its method uses both the smooth category and the presence of boundary. For example, $(m, n) = (21, 23)$ satisfies the hypotheses since $11 \cdot 21 = 231 = 10 \cdot 23 + 1$; the proof in the source produces, for every even $c$, the undecidable case $(m, n) = (10c + 1, 11c + 1)$.

## Depends on

- [Homeomorphism](../../topological-spaces/homeomorphism.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Smooth immersibility of manifolds in Euclidean space is undecidable in a range of even codimension](smooth-immersibility-is-undecidable.md)

## Expansion

The proof reduces from the undecidability of smooth immersibility (clause (ii) of the immersion theorem). For $n \ge m + 2$, a manifold $M$ immerses smoothly in $\mathbb R^n$ iff $M \times D^k$ immerses smoothly in $\mathbb R^{n+k}$. In general position the self-intersection of an immersion $M \to \mathbb R^n$ is a $(2m - n)$-dimensional complex, which embeds in $\mathbb R^k$ once $k \ge 4m - 2n + 1$; pushing a neighborhood of the self-intersection off itself in the $\mathbb R^k$ direction then deforms $f \times \mathrm{id} : M \times D^k \to \mathbb R^{n+k}$ into an embedding. Conversely, if $M$ does not immerse in $\mathbb R^n$, then $M \times D^k$ does not embed in $\mathbb R^{n+k}$. With $m = 4c$, $n = 5c$ and $k = 6c + 1$ this shows that embeddability of $(10c + 1)$-manifolds with boundary in $\mathbb R^{11c + 1}$ is undecidable for even $c$. A good expansion links the stability of immersibility under products with discs and the general-position step that turns $f \times \mathrm{id}$ into an embedding.

## Sources

- Fedor Manin and Shmuel Weinberger, *Algorithmic aspects of immersibility and embeddability*, Int. Math. Res. Not. IMRN 2024, no. 17, 12433–12454, https://doi.org/10.1093/imrn/rnae170, read in the copy arXiv:1812.09413v4, whose numbering is used here: the input model is Section 2.2.1; the statement is Theorem 4.2 in Subsection 4.2 ("Embeddability is undecidable") of Section 4 ("Applications to embeddings"), proved by reduction to Theorem 3.1(ii).
