# Chan–Vassilevska Williams–Xu: ACP Triangle Collection needs n^{2.25-o(1)} time under Real APSP, Real 3SUM or OV

Assume at least one of the following holds: the Orthogonal Vectors hypothesis, the Real 3SUM hypothesis, or the Real APSP hypothesis. Then All-Color-Pairs Triangle Collection on $n$-vertex graphs requires $n^{2+\delta-o(1)}$ time for some constant $\delta > 0$, in a reasonable Real RAM model; the reductions give $\delta=1/4$, i.e. a lower bound of $n^{2.25-o(1)}$. Moreover, assuming only the OV hypothesis, Triangle Collection itself requires $n^{3-o(1)}$ time. Combined with the reductions of Abboud, Vassilevska Williams and Yu, this gives polynomial conditional lower bounds, for some constant $\delta > 0$, for ST-Max-Flow and for fully dynamic Max-Flow and counting versions of reachability and strong connectivity, now under the weaker disjunctive hypothesis.

## Proof sketch

The Real APSP and Real 3SUM parts go through the All-Edges Sparse Triangle lower bounds and a reduction from All-Edges Monochromatic Triangle to a "light" variant of ACP-Tri-Co. The OV part reduces OV to a colourful variant of Boolean matrix multiplication (deciding, for each output entry, whether all colours appear among the witnesses) and embeds it into ACP-Tri-Co, which also shows that Tri-Co is equivalent to a simpler restricted version.

## Depends on

- [Triangle Collection and All-Color-Pairs Triangle Collection](triangle-collection-and-all-color-pairs.md)
- [Real RAM, the Real 3SUM hypothesis and the Real APSP hypothesis](real-ram-real-3sum-real-apsp-hypotheses.md)

## Proof depends on

- [Chan–Vassilevska Williams–Xu: All-Edges Sparse Triangle lower bounds from Real APSP, Real Exact Triangle and Real 3SUM](chan-vassilevska-williams-xu-all-edges-sparse-triangle.md)
- [SETH implies the Orthogonal Vectors hypothesis](../fine-grained-hypotheses/seth-implies-the-orthogonal-vectors-hypothesis.md)
- [Abboud–Vassilevska Williams–Yu: Triangle Collection needs cubic time unless 3SUM, APSP and SETH all fail](abboud-vassilevska-williams-yu-triangle-collection.md)

## Sources

- Timothy M. Chan, Virginia Vassilevska Williams and Yinzhan Xu, "Hardness for Triangle Problems under Even More Believable Hypotheses: Reductions from Real APSP, Real 3SUM, and OV", STOC (2022), arXiv:2203.08356.
