# Consistency of two-dimensional combinatorial substitutions is undecidable

No algorithm decides whether a given two-dimensional combinatorial substitution is consistent, that is, whether the relative placement of the images of cells never depends on the chain of concatenation rules used to compute it.

**Theorem.** It is undecidable, given a two-dimensional [combinatorial substitution](combinatorial-substitutions-and-consistency.md) $\sigma$, whether $\sigma$ is consistent.

The proof gives the stronger statement that consistency is undecidable for two-dimensional domino-to-domino substitutions, and a modification shows it is undecidable for non-overlapping substitutions as well (Remark 3.2 of the source). The source notes that the proofs adapt to higher dimensions but not to dimension one.

## Depends on

- [Combinatorial substitutions, consistency and overlapping](combinatorial-substitutions-and-consistency.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the *weak cycle tiling problem* for Wang tiles, shown undecidable by Kari: does a finite set $T$ of Wang tiles admit a nontrivial cycle $(a_1, \dots, a_n)$ of translated tiles in which consecutive tiles share exactly one edge with matching colors and $a_n = a_1$, the other tiles being distinct? From $T$ one builds a domino-to-domino substitution $\sigma$ on the alphabet $T \times \{\rightarrow, \uparrow, \leftarrow, \downarrow\}$, each base pattern a single cell at the origin. Its concatenation rules are given for color-matching dominoes in which exactly one cell points at the other, and they place the image of the pointing cell immediately to the left of the image of the pointed cell. A valid tiling of a cycle $(a_1, \dots, a_n)$ gives a loop of cells, each pointing at the next, whose image vector is $(n - 1, 0) \ne (0, 0)$, so $\sigma$ is inconsistent; conversely, if $T$ admits no tiling of a cycle there is no simple loop of starting patterns, and $\sigma$ is consistent by the loop characterization of consistency (Proposition 2.2 of the source). Hence $\sigma$ is consistent if and only if $T$ admits no tiling of a cycle.

## Sources

- T. Jolivet and J. Kari, "Consistency of multidimensional combinatorial substitutions", *Theoretical Computer Science* 454:178–188, 2012, doi:[10.1016/j.tcs.2012.03.050](https://doi.org/10.1016/j.tcs.2012.03.050); numbering of arXiv:1112.1841v2: Theorem 3.1 with its proof and Remark 3.2 in Section 3, and Proposition 2.2 (characterization of consistency by loops).
