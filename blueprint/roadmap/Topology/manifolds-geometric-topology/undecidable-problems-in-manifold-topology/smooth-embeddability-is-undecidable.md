# Smooth embeddability of manifolds with boundary in Euclidean space is undecidable in a range of even codimension

Let $n - m$ be even with $11m \ge 10n + 1$. There is no algorithm that decides whether a given smooth $m$-manifold with boundary embeds smoothly in $\mathbb{R}^n$.

Smooth $m$-manifolds with boundary are given as inputs by finite data, for example as semialgebraic subsets of some $\mathbb{R}^N$ defined by polynomials with rational coefficients. A smooth *embedding* of $M$ in $\mathbb{R}^n$ is an immersion that is a homeomorphism onto its image.

**Theorem (Manin–Weinberger).** Let $m < n$ be natural numbers with $n - m$ even and $11m \ge 10n + 1$. Then there is no algorithm that decides, for a given smooth $m$-manifold $M$ with boundary, whether $M$ embeds smoothly in $\mathbb{R}^n$.

Conventions: the dimensions are fixed and the manifold is the input; manifolds with nonempty boundary are allowed, and the source notes that its method uses both the smooth category and the presence of boundary. For example, $(m, n) = (21, 23)$ satisfies the hypotheses since $11 \cdot 21 = 231 = 10 \cdot 23 + 1$; the proof in the source produces, for every even $c$, the undecidable case $(m, n) = (10c + 1, 11c + 1)$.

## Depends on

None.

## Proof depends on

- [Smooth immersibility of manifolds in Euclidean space is undecidable in a range of even codimension](smooth-immersibility-is-undecidable.md)

## Expansion

The proof reduces from the undecidability of smooth immersibility (clause (ii) of the immersion theorem). For $n \ge m + 2$, a manifold $M$ immerses smoothly in $\mathbb R^n$ iff $M \times D^k$ immerses smoothly in $\mathbb R^{n+k}$. In general position the self-intersection of an immersion $M \to \mathbb R^n$ is a $(2m - n)$-dimensional complex, which embeds in $\mathbb R^k$ once $k \ge 4m - 2n + 1$; pushing a neighborhood of the self-intersection off itself in the $\mathbb R^k$ direction then deforms $f \times \mathrm{id} : M \times D^k \to \mathbb R^{n+k}$ into an embedding. Conversely, if $M$ does not immerse in $\mathbb R^n$, then $M \times D^k$ does not embed in $\mathbb R^{n+k}$. With $m = 4c$, $n = 5c$ and $k = 6c + 1$ this shows that embeddability of $(10c + 1)$-manifolds with boundary in $\mathbb R^{11c + 1}$ is undecidable for even $c$.

## Sources

- Fedor Manin and Shmuel Weinberger, *Algorithmic aspects of immersibility and embeddability*, Int. Math. Res. Not. IMRN 2024, no. 17, 12433–12454, https://doi.org/10.1093/imrn/rnae170, read in the copy arXiv:1812.09413v4, whose numbering is used here: the statement is Theorem 11 in the subsection "Embeddability is undecidable" of its section on applications to embeddings, proved by reduction to Theorem 8(ii).
