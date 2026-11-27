# Snake problems on ℤ^d are undecidable for every generating set

For every $d\ge2$ and every finite generating set of $\mathbb Z^d$, the infinite snake problem and the ouroboros problem are undecidable.

**Theorem.** Let $d\ge2$ and let $S$ be any finite generating set of $\mathbb Z^d$. The infinite snake problem and the ouroboros problem for $(\mathbb Z^d,S)$, in the sense of [domino snake problems](domino-snake-problems-on-groups.md), are undecidable.

## Depends on

- [Domino snake problems on finitely generated groups](domino-snake-problems-on-groups.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

A *snake embedding* of $(G,S)$ into $(H,T)$ is a map $G\to H$ computed on words over $S\cup S^{-1}$ by an invertible-reversible transducer, such that two words have equal images in $H$ exactly when they are equal in $G$. Such an embedding gives many-one reductions of the infinite snake and ouroboros problems on $(G,S)$ to those on $(H,T)$. Two generators of $S$ with trivially intersecting cyclic subgroups span a copy of $\mathbb Z^2$, which receives an obvious snake embedding from $\mathbb Z^2$ with its standard generators, and the problems transfer from a finitely generated subgroup to the whole group. On $\mathbb Z^2$ with standard generators the infinite snake problem is $\Pi^0_1$-complete (Adleman, Kari, Kari and Reishus) and the ouroboros problem is $\Sigma^0_1$-complete (Ebbinghaus; Kari).

## Sources

- Nathalie Aubrun and Nicolas Bitar, "Domino Snake Problems on Groups", in *Fundamentals of Computation Theory (FCT 2023)*, Lecture Notes in Computer Science 14292, Springer, 2023, pp. 46–59, doi:[10.1007/978-3-031-43587-4_4](https://doi.org/10.1007/978-3-031-43587-4_4); read in arXiv:2307.12655v1 ([arXiv](https://arxiv.org/abs/2307.12655v1)), whose numbering is used: Section 5 (Snake Embeddings): Definitions 7 and 8, Proposition 7 (the reduction) and Proposition 8 ($\mathbb Z^d$ for all generating sets); Theorem 1 in Section 3 for the recalled results on $\mathbb Z^2$.
