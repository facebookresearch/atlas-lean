# Abboud–Fischer–Kelley–Lovett–Meka: efficient grid-regularity decomposition with quasipolynomially many parts

Call $A\in\{0,1\}^{X\times Y}$ **$(\varepsilon,k,\ell)$-regular** if $\|A\|_{U(k,\ell)}\le(1+\varepsilon)\,\mathbb{E}[A]$, and **$\varepsilon$-min-degree** if every row $x\in X$ has density at least $(1-\varepsilon)\,\mathbb{E}[A]$. For every $A\in\{0,1\}^{X\times Y}$, $\varepsilon\in(0,1)$ and $d\ge1$ there are rectangles $X_i\times Y_i\subseteq X\times Y$ and matrices $A_i\in\{0,1\}^{X_i\times Y_i}$, $i\le L$, such that $A=\sum_i A_i$, $\sum_i|X_i||Y_i|\le(d+2)|X||Y|$, each $A_i$ either has density at most $2^{-d}$ or is $(\varepsilon,2,d)$-regular and $\varepsilon$-min-degree, and $L\le\exp(d^3\,\mathrm{poly}(1/\varepsilon))$. For a pair $A\in\{0,1\}^{X\times Y}$, $B\in\{0,1\}^{Y\times Z}$ there is a simultaneous decomposition $AB=\sum_{j\le K}A_jB_j$ on boxes $X_j\times Y_j\times Z_j$ with $\sum_j|X_j||Y_j||Z_j|\le2(d+2)^2|X||Y||Z|$, in which for each $j$ one of $A_j$, $B_j$ has density at most $2^{-d}$ or both $A_j$ and $B_j^{\top}$ are $(\varepsilon,2,d)$-regular and $\varepsilon$-min-degree, with $K\le\exp(d^7\,\mathrm{poly}(1/\varepsilon))$; for fixed $\varepsilon$ and density threshold $\delta=2^{-d}$ this is $2^{O((\log\delta^{-1})^{7})}$ parts, quasipolynomial in $\delta^{-1}$, in contrast with tower-type bounds for Szemerédi regularity. Both decompositions are computed by deterministic algorithms running in time $n^2\exp(d^3\,\mathrm{poly}(1/\varepsilon))$ and $n^2\exp(d^7\,\mathrm{poly}(1/\varepsilon))$ respectively, where $n$ is the total number of vertices; in particular grid norms $\|A\|_{U(k,\ell)}$ are approximated deterministically to within the needed precision.

## Proof sketch

A density-increment argument: if a piece is not grid-regular, then its large grid norm, via a Kelley–Meka-style "sifting" lemma, yields a large combinatorial subrectangle on which the density increases by a factor $1+\varepsilon/2$; since pieces that are refined have density at least $2^{-d}$ and density is at most 1, each piece is refined at most $O(d/\varepsilon)$ times along any chain, which bounds the number of parts. Deterministic estimation of grid norms replaces random sampling to make the procedure algorithmic.

## Depends on

- [Grid norms and grid regularity of Boolean matrices (Kelley–Lovett–Meka)](grid-norms-and-grid-regularity.md)

## Proof depends on

- [Kelley–Meka: Roth numbers are below every power of the logarithm](../../../Combinatorics/additive-combinatorics/progressions-dense-sets/bounds-for-roth-numbers/roth-number-log-power-decay-holds.md)

## Sources

- Amir Abboud, Nick Fischer, Zander Kelley, Shachar Lovett and Raghu Meka, "New Graph Decompositions and Combinatorial Boolean Matrix Multiplication Algorithms", STOC (2024), arXiv:2311.09095.
- Zander Kelley, Shachar Lovett and Raghu Meka, "Explicit separations between randomized and deterministic Number-on-Forehead communication", ECCC TR23-124 (2023), arXiv:2308.12451.
