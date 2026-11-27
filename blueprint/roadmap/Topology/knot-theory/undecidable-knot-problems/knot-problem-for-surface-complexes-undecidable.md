# Deciding whether a curve in a surface complex is knotted is undecidable

There is no algorithm that decides, for a polygonal simple closed curve $c$ in a finite $2$-dimensional complex $K$, whether $c$ is knotted in $K$; the set of unknotted pairs is complete recursively enumerable.

Let $K$ be a finite surface complex, a finite $2$-dimensional complex in the sense of the source (in the proof, $K$ is triangulated as a $2$-dimensional simplicial complex), and $c$ a simple polygonal closed curve in $K$. Two simple edge paths are *simplicially isotopic* with respect to a simplicial decomposition $\Sigma$ of $K$ if one is obtained from the other by a finite sequence of simple edge paths, each obtained from the previous one by pulling it across a triangle of $\Sigma$ from one side to the other. The curve $c$ is *unknotted* in $K$ if, for some simplicial decomposition of $K$, it is simplicially isotopic to a curve that bounds a disk in $K$, and *knotted* otherwise.

**Theorem (Stillwell).** The set of pairs $(K, c)$ with $c$ an unknotted simple polygonal curve in the finite surface complex $K$ is complete recursively enumerable. Consequently there is no algorithm that decides whether a given simple polygonal curve in a finite surface complex is knotted.

Conventions: knotting is defined through simplicial isotopies in subdivisions of $K$ rather than arbitrary isotopies, because, as in Alexander's example for classical knots, a general isotopy can shrink a knotted arc to a point; by the Hauptvermutung for surface complexes, $c$ is unknotted exactly when it is simplicially unknotted in a sufficiently fine subdivision, for example a high barycentric subdivision.

## Depends on

- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../../GroupTheory/presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

The set of unknotted pairs is recursively enumerable: for a fixed subdivision there are only finitely many simplicial isotopies to search, and one runs through successive barycentric subdivisions. Completeness comes from a reduction of the word problem for finitely presented groups. Given a presentation $G$ and a word $w$, one builds, following Dehn's realization of a presentation by a $2$-complex, a surface complex $K(G)$ from annuli $A_i$, one for each generator, meeting along a common transverse segment, a square, and disks $D_j$, one for each relator. The word $w$ is realized as a simple curve $c(w)$ running around the annuli. Isotopies across the disks insert or delete relators in the word, and isotopies within the annuli insert or delete trivial relators, so $c(w)$ is unknotted in $K(G)$ if and only if $w = 1$ in $G$. Since there are finitely presented groups with unsolvable word problem, knotting is undecidable.

## Sources

- John C. Stillwell, *Unsolvability of the knot problem for surface complexes*, Bull. Austral. Math. Soc. 20 (1979), no. 1, 131–137, https://doi.org/10.1017/S000497270000914X, read in the open-access copy at <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/1606629E4F78A69D919B5F3C4E93774C/S000497270000914Xa.pdf/div-class-title-unsolvability-of-the-knot-problem-for-surface-complexes-div.pdf>: the statement is in the abstract and the paragraph before Theorem 1, and the reduction is Theorem 1 there.
