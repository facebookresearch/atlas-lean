# Abboud–Vassilevska Williams–Yu: Triangle Collection needs cubic time unless 3SUM, APSP and SETH all fail

Assume at least one of the following holds: SETH, the (integer) 3SUM hypothesis, or the (integer) APSP hypothesis. Then for every $\varepsilon > 0$ there is no $O(n^{3-\varepsilon})$-time algorithm for Triangle Collection on $n$-vertex graphs (word RAM). Via reductions from Triangle Collection this yields lower bounds, under the same disjunctive assumption, for problems such as dynamic and static variants of maximum flow and connectivity, which are thus "hard under an extremely popular conjecture": refuting the lower bound would refute all three hypotheses simultaneously.

## Proof sketch

From integer 3SUM and integer APSP one reduces to the integer Exact Triangle problem (find a triangle of total weight 0), and an Exact Triangle instance with weights in $\pm[n^c]$ is converted into a Tri-Co instance by hashing weights into colour classes so that a zero-weight triangle corresponds to a missing colour triple. From SETH one reduces 3-OV (three vectors with no coordinate where all three are 1) to Tri-Co by colouring vertices with vectors and using coordinate gadgets.

## Depends on

- [Triangle Collection and All-Color-Pairs Triangle Collection](triangle-collection-and-all-color-pairs.md)
- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)
- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [Fine-grained reductions](../fine-grained-hypotheses/fine-grained-reductions.md)

## Sources

- Amir Abboud, Virginia Vassilevska Williams and Huacheng Yu, "Matching Triangles and Basing Hardness on an Extremely Popular Conjecture", STOC (2015).
