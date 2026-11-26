# Grid norms and grid regularity of Boolean matrices (Kelley–Lovett–Meka)

For a function $A:X\times Y\to\mathbb{R}_{\ge 0}$ on finite sets and integers $k,\ell\ge 1$, the **$(k,\ell)$-grid norm** is

$$
\|A\|_{U(k,\ell)}=\Bigl(\mathbb{E}_{x_1,\dots,x_k\in X}\ \mathbb{E}_{y_1,\dots,y_\ell\in Y}\ \prod_{i=1}^{k}\prod_{j=1}^{\ell}A(x_i,y_j)\Bigr)^{1/(k\ell)}.
$$

For a Boolean matrix (bipartite graph) $A$ of density $\delta=\mathbb{E}[A]$ one always has $\|A\|_{U(k,\ell)}\ge\delta$, with near-equality for random-like matrices. A matrix is **grid-regular** (with parameters $k,\ell,\varepsilon$) if $\|A\|_{U(k,\ell)}\le(1+\varepsilon)\delta$, i.e. it has no dense "combinatorial rectangle" structure detectable by $k\times\ell$ grids. This weak pseudorandomness notion, introduced by Kelley, Lovett and Meka in communication complexity and related to the spreadness notions behind the Kelley–Meka bound for 3-term progressions, has the key property that the product of two grid-regular matrices is close to uniform: in a three-layer graph whose two edge sets are grid-regular, the number of 2-paths between most left-right pairs is close to its expectation.

## Sources

- Zander Kelley, Shachar Lovett and Raghu Meka, "Explicit separations between randomized and deterministic Number-on-Forehead communication", ECCC TR23-124 (2023), arXiv:2308.12451.
- Amir Abboud, Nick Fischer, Zander Kelley, Shachar Lovett and Raghu Meka, "New Graph Decompositions and Combinatorial Boolean Matrix Multiplication Algorithms", STOC (2024), arXiv:2311.09095.
- Zander Kelley and Raghu Meka, "Strong Bounds for 3-Progressions", FOCS (2023), arXiv:2302.05537.
