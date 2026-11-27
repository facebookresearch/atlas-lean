# Overlapping of consistent two-dimensional combinatorial substitutions is undecidable

No algorithm decides, for a given two-dimensional combinatorial substitution that is known to be consistent, whether the images of two distinct cells can overlap.

**Theorem.** It is undecidable, given a consistent two-dimensional [combinatorial substitution](combinatorial-substitutions-and-consistency.md) $\sigma$, whether $\sigma$ is overlapping, that is, whether it fails to be non-overlapping.

The proof gives undecidability already for consistent two-dimensional domino substitutions, and the source states that it holds even for domino-to-domino substitutions (Remark 3.4).

## Depends on

- [Combinatorial substitutions, consistency and overlapping](combinatorial-substitutions-and-consistency.md)

## Proof depends on

None.

## Expansion

The proof again reduces the weak cycle tiling problem for Wang tiles (Kari). For a tile set $T$ and two tiles $a, b$ whose colors match when $b$ is placed to the right of $a$, a domino substitution $\sigma_{a,b}$ on $T \cup \{a_0, b_0\}$, with two new types $a_0, b_0$ and single-cell base patterns, is built so that it is consistent and an overlap can only occur between the images of a cell of type $a_0$ and a cell of type $b_0$. Such an overlap occurs if and only if $T$ has a valid tiling of a cycle containing the domino formed by $a$ and $b$, because the domino of $a_0$ and $b_0$ is not itself a starting pattern and its image is computed only around such a cycle. Computing $\sigma_{a,b}$ for every matching pair, some $\sigma_{a,b}$ is overlapping if and only if $T$ admits a tiling of a cycle.

## Sources

- T. Jolivet and J. Kari, "Consistency of multidimensional combinatorial substitutions", *Theoretical Computer Science* 454:178–188, 2012, doi:[10.1016/j.tcs.2012.03.050](https://doi.org/10.1016/j.tcs.2012.03.050); numbering of arXiv:1112.1841v2: Theorem 3.3 with its proof and Remark 3.4 in Section 3.
