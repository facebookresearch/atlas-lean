# Snake problems on virtually nilpotent groups are undecidable for some generating set

Every finitely generated infinite virtually nilpotent group that is not virtually cyclic has a finite generating set for which the infinite snake problem and the ouroboros problem are undecidable.

**Theorem.** Let $G$ be a finitely generated infinite nilpotent group that is not virtually $\mathbb Z$, and $S$ a finite generating set. Then there is $g\in G$ such that the infinite snake problem and the ouroboros problem for $(G,S\cup\{g\})$, in the sense of [domino snake problems](domino-snake-problems-on-groups.md), are undecidable.

**Corollary.** Every finitely generated infinite virtually nilpotent group $G$ that is not virtually $\mathbb Z$ has a finite generating set $S$ for which the infinite snake problem and the ouroboros problem for $(G,S)$ are undecidable.

The statement is existential in the generating set: the source does not claim undecidability for every generating set of a nilpotent group, as it does for $\mathbb Z^d$.

## Depends on

- [Domino snake problems on finitely generated groups](domino-snake-problems-on-groups.md)

## Proof depends on

- [Snake problems on ℤ^d are undecidable for every generating set](snake-problems-on-z-d-are-undecidable.md)

## Expansion

If $G$ has an element $g$ of infinite order in its center and $G/\langle g\rangle$ is not a torsion group, there is a snake embedding of $\mathbb Z^2$ with its standard generators into $(G,S\cup\{g\})$: one copy of $\mathbb Z$ is $\langle g\rangle$, and the other comes from a periodic point of the skeleton subshift of $(G,S)$, which exists because $G$ is not a torsion group. A finitely generated infinite nilpotent group has a torsion-free central element $g$; no quotient of it is an infinite torsion group, and $G/\langle g\rangle$ is infinite when $G$ is not virtually cyclic. The undecidability for $\mathbb Z^2$ then transfers through the embedding, and to finite-index overgroups.

## Sources

- Nathalie Aubrun and Nicolas Bitar, "Domino Snake Problems on Groups", in *Fundamentals of Computation Theory (FCT 2023)*, Lecture Notes in Computer Science 14292, Springer, 2023, pp. 46–59, doi:[10.1007/978-3-031-43587-4_4](https://doi.org/10.1007/978-3-031-43587-4_4); read in arXiv:2307.12655v1 ([arXiv](https://arxiv.org/abs/2307.12655v1)), cited by section because its theorem counters are not recoverable from the source files: Section 6 (virtually nilpotent groups): the lemma on central elements of infinite order, the propositions preceding the theorem, the theorem on nilpotent groups and its corollary on virtually nilpotent groups.
