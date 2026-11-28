# Chan–Vassilevska Williams–Xu: All-Edges Sparse Triangle lower bounds from Real APSP, Real Exact Triangle and Real 3SUM

In **All-Edges Sparse Triangle** (AE-Sparse-Tri) one is given an $m$-edge graph and must decide, for every edge, whether it lies in a triangle. On a reasonable Real RAM:

- AE-Sparse-Tri requires $m^{4/3-o(1)}$ time assuming the Real APSP hypothesis;
- it requires $m^{5/4-o(1)}$ time assuming the Real Exact-Triangle hypothesis (no $O(n^{3-\varepsilon})$ algorithm decides whether an $n$-vertex graph with real edge weights has a triangle of total weight 0);
- it requires $m^{6/5-o(1)}$ time assuming the Real 3SUM hypothesis.

Previously such bounds were known only from the integer hypotheses. Since many problems (dynamic reachability, dynamic shortest paths, Pagh's problem) were shown hard via AE-Sparse-Tri, they inherit hardness under the real hypotheses.

## Proof sketch

Hashing-based reductions do not work for reals, so the reductions instead use "Fredman's trick": $a_i+b_j\le a_{i'}+b_{j'}$ iff $a_i-a_{i'}\le b_{j'}-b_j$, which turns comparisons of sums into comparisons of differences that can be sorted and grouped combinatorially. Real APSP is reduced to (min,+)-products and then to many sparse triangle-listing instances on the induced comparison structure; Real 3SUM is first reduced to Real Exact Triangle and then to AE-Sparse-Tri.

## Depends on

- [Real RAM, the Real 3SUM hypothesis and the Real APSP hypothesis](real-ram-real-3sum-real-apsp-hypotheses.md)

## Sources

- Timothy M. Chan, Virginia Vassilevska Williams and Yinzhan Xu, "Hardness for Triangle Problems under Even More Believable Hypotheses: Reductions from Real APSP, Real 3SUM, and OV", STOC (2022), arXiv:2203.08356.
