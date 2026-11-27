# The domino problem is undecidable on every rhombus subshift

For every nonempty subshift of edge-to-edge rhombus tilings, such as the Penrose subshift, the domino problem with color-matching rhombus tiles is co-r.e.-hard, hence undecidable; for effective subshifts it is co-r.e.-complete.

**Theorem.** Let $X$ be a nonempty rhombus subshift on a finite shapeset $\mathcal S$. Then [$\mathrm{Domino}(X)$](domino-problem-on-a-rhombus-subshift.md) is $\Pi^0_1$-hard (co-r.e.-hard) under many-one reductions; in particular it is undecidable. If moreover $X$ is effective, then $\mathrm{Domino}(X)$ is $\Pi^0_1$-complete, many-one equivalent to the classical domino problem on $\mathbb Z^2$.

No computability assumption on $X$ is needed for hardness. When the forbidden patterns of $X$ are given as an oracle, the problem lies in $\Pi^0_1$ relative to that oracle, but hardness relative to the oracle is not established.

## Depends on

- [The domino problem on a rhombus subshift](domino-problem-on-a-rhombus-subshift.md)
- [Co-recognizability by single-tape machines](../../../turing-machines/single-tape/decidable-and-recognizable-predicates-on-single/single-tape-co-recognizable.md)

## Proof depends on

- [The tiling problem is undecidable](../the-tiling-problem-is-undecidable.md)

## Expansion

Membership in $\Pi^0_1$ for effective $X$: by compactness a tiling exists iff, for every radius $r$, some patch of radius $r$ is locally allowed, i.e. avoids the color constraints and the first $r$ forbidden patterns, and these finitely many patches are computable. For hardness, a compactness argument gives a subset $\mathcal S'\subseteq\mathcal S$ such that $X'=X\cap X_{\mathcal S'}$ is nonempty and some shape $r\in\mathcal S'$ occurs uniformly recurrently in every tiling of $X'$. Occurrences of $r$ are the crossings of two families of chains of rhombuses (bi-infinite sequences sharing an edge direction), and uniform recurrence lets them be indexed by $\mathbb Z^2$ so that consecutive occurrences along a chain are adjacent. A classical Wang tileset is copied onto the shape $r$; link tiles on the shapes sharing one edge direction with $r$ carry a color along the chain, and all other shapes get a neutral blank color. Hence the classical domino problem, $\Pi^0_1$-complete by Berger's theorem, reduces to $\mathrm{Domino}(X')$. Finally $\mathrm{Domino}(X')$ reduces to $\mathrm{Domino}(X)$ by adding, for each shape outside $\mathcal S'$, one tile with fresh colors, which can never be used. The choice of $\mathcal S'$ need not be computable from $X$; only the reduction for fixed $\mathcal S'$ must be.

## Sources

- Benjamin Hellouin de Menibus, Victor H. Lutfalla and Camille Noûs, "The Domino Problem Is Undecidable on Every Rhombus Subshift", in *Developments in Language Theory (DLT 2023)*, Lecture Notes in Computer Science 13911, Springer, 2023, pp. 100–112, doi:[10.1007/978-3-031-33264-7_9](https://doi.org/10.1007/978-3-031-33264-7_9); numbering of arXiv:2302.12086v1 ([arXiv](https://arxiv.org/abs/2302.12086v1)): the main theorem of Section 1; Section 3: the proposition that $\mathrm{Domino}(X)$ is in $\Pi^0_1$ for effective $X$ (Section 3.1), the hardness for subshifts with a uniformly recurrent shape (Section 3.2), and the theorem of Section 3.3 (every nonempty rhombus subshift) with the remarks after it.
