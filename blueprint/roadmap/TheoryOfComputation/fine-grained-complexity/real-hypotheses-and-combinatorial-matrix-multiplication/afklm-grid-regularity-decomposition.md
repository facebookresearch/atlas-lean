# Abboud–Fischer–Kelley–Lovett–Meka: efficient grid-regularity decomposition with quasipolynomially many parts

Every Boolean matrix (equivalently, bipartite graph) can be decomposed into a collection of submatrices on combinatorial rectangles, together with a sparse remainder, such that each piece is grid-regular relative to its own density; the number of pieces needed for regularity parameter $\delta$ is quasipolynomial, $2^{O((\log\delta^{-1})^{7})}$, in contrast with tower-type bounds for Szemerédi regularity and $2^{O(\delta^{-2})}$ for Frieze–Kannan regularity. The decomposition is computed by an efficient deterministic algorithm, which in particular approximates grid norms $\|A\|_{U(k,\ell)}$ deterministically to within the needed precision.

## Proof sketch

A density-increment argument: if a piece is not grid-regular, then its large grid norm, via a Kelley–Meka-style "sifting" lemma, yields a large combinatorial subrectangle on which the density increases by a constant factor; since density is at most 1, each piece is refined only $O(\log\delta^{-1})$-ish many times along any chain, with each refinement costing quasipolynomially many parts. Deterministic estimation of grid norms replaces random sampling to make the procedure algorithmic.

## Depends on

- [Grid norms and grid regularity of Boolean matrices (Kelley–Lovett–Meka)](grid-norms-and-grid-regularity.md)

## Proof depends on

- [Kelley–Meka: Roth numbers are below every power of the logarithm](../../../Combinatorics/additive-combinatorics/progressions-dense-sets/bounds-for-roth-numbers/roth-number-log-power-decay-holds.md)

## Sources

- Amir Abboud, Nick Fischer, Zander Kelley, Shachar Lovett and Raghu Meka, "New Graph Decompositions and Combinatorial Boolean Matrix Multiplication Algorithms", STOC (2024), arXiv:2311.09095.
- Zander Kelley, Shachar Lovett and Raghu Meka, "Explicit separations between randomized and deterministic Number-on-Forehead communication", ECCC TR23-124 (2023), arXiv:2308.12451.
