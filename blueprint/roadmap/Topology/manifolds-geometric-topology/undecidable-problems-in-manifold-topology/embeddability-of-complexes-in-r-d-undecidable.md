# Embeddability of d- and (d−1)-dimensional complexes in d-space is undecidable for d at least five

For every $d \ge 5$ there is no algorithm that decides whether a given finite simplicial complex of dimension at most $d - 1$ admits a piecewise-linear embedding in $\mathbb{R}^d$; hence the same holds for complexes of dimension at most $d$.

For integers $k \le d$, the problem $\mathrm{EMBED}_{k \to d}$ takes as input a finite simplicial complex $K$ of dimension at most $k$ and asks whether there is a piecewise-linear (PL) embedding of $|K|$ into $\mathbb{R}^d$.

**Theorem (Matoušek–Tancer–Wagner).** For every $d \ge 5$, the problem $\mathrm{EMBED}_{(d-1) \to d}$, and hence also $\mathrm{EMBED}_{d \to d}$, is algorithmically undecidable.

Conventions: the dimension $d$ is fixed and the complex is the input. In contrast, $\mathrm{EMBED}_{k \to 2}$ for $k = 1, 2$ and $\mathrm{EMBED}_{k \to 2k}$ for $k \ge 3$ are solvable in polynomial time, and the same paper shows that $\mathrm{EMBED}_{k \to d}$ is NP-hard for $d \ge 4$ and $d \ge k \ge (2d - 2)/3$. As a consequence of the theorem, for every computable function $f$ there are $(d-1)$-dimensional complexes with $n$ simplices that PL-embed in $\mathbb{R}^d$ but have no linearly embeddable subdivision with at most $f(n)$ simplices.

## Depends on

- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The n-sphere is algorithmically unrecognizable for n at least five](sphere-recognition-is-undecidable.md)

## Expansion

By Novikov's theorem in the form of Theorem 3.1 of the source (whose detailed proof is in the appendix of Nabutovsky's paper), there is, for fixed $d \ge 5$, an effectively constructible sequence of simplicial complexes $\Sigma_i$, each a homology $d$-sphere, such that each $\Sigma_i$ is either a PL $d$-sphere or has nontrivial fundamental group, and no algorithm decides which case holds. Let $K_i$ be the $(d-1)$-skeleton of $\Sigma_i$. A lemma of the source shows, for a homology $d$-sphere $\Sigma$ with $(d-1)$-skeleton $K$: if $\Sigma$ is a PL sphere then $K$ PL-embeds in $\mathbb{R}^d$, and if $K$ PL-embeds in $\mathbb{R}^d$ then $\Sigma$ is homeomorphic to $S^d$; the second part uses Lefschetz duality and a weak PL Schoenflies theorem. So deciding embeddability of the $K_i$ would separate the two cases. A good expansion links this lemma, Lefschetz and Alexander duality and the weak PL Schoenflies theorem.

## Sources

- Jiří Matoušek, Martin Tancer and Uli Wagner, *Hardness of embedding simplicial complexes in $\mathbb{R}^d$*, J. Eur. Math. Soc. (JEMS) 13 (2011), no. 2, 259–295, https://doi.org/10.4171/JEMS/252, read in the copy arXiv:0807.0336v2: the statement is Theorem 1.1 there, the consequence on subdivisions is the corollary after it, and the proof is in Section 3 ("Undecidability: Proof of Theorem 1.1"), combining Novikov's theorem as quoted there (Theorem 3.1) with Lemma 3.3, which relates embeddings of the skeleton to sphere recognition, and Lemma 3.2.
