# Triangle Collection and All-Color-Pairs Triangle Collection

In **Triangle Collection** (Tri-Co) the input is an $n$-vertex graph $G$ with a colouring $c:V(G)\to\Gamma$ of its vertices, and the question is whether for **every** triple of distinct colours $a,b,c'\in\Gamma$ there is a triangle in $G$ whose vertices have colours $a,b,c'$. In **All-Color-Pairs Triangle Collection** (ACP-Tri-Co) the input is the same and the algorithm must output, for every pair of distinct colours $(a,b)$, whether for every colour $c'\notin\{a,b\}$ there is a triangle with colours $(a,b,c')$. Tri-Co reduces to ACP-Tri-Co trivially; both are solvable in $O(n^3)$ time by listing triangles, and the output of Tri-Co is a single bit even though it quantifies over all colour triples.

## Depends on

- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)

## Sources

- Amir Abboud, Virginia Vassilevska Williams and Huacheng Yu, "Matching Triangles and Basing Hardness on an Extremely Popular Conjecture", STOC (2015).
- Timothy M. Chan, Virginia Vassilevska Williams and Yinzhan Xu, "Hardness for Triangle Problems under Even More Believable Hypotheses: Reductions from Real APSP, Real 3SUM, and OV", STOC (2022), arXiv:2203.08356.
