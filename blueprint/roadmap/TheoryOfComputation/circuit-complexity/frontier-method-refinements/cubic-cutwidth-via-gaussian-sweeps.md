# Cutwidth and bisection bounds for cubic graphs via median-switched Gaussian sweeps

Let $c_3=\frac{3}{4\pi}\arccos\frac56\approx0.139822$. For every $\varepsilon>0$ and every finite loopless $3$-regular multigraph $G$ on $n$ vertices (for $n$ large), there is a linear layout of width at most $(c_3+\varepsilon)n$, and a bisection of $V(G)$ cutting at most $(c_3+\varepsilon)n$ edges. For connected subcubic multigraphs this gives layouts of width at most $(2c_3+o(1))\beta_1(G)+o(n)$, i.e. the layout hypothesis $\mathrm{LB}(3,2c_3)$.

## Proof sketch

Assign each vertex a Gaussian score from a random embedding (a Gaussian sweep) and order vertices by score, switching the two endpoints of a matched edge around the median when advantageous; the probability that a given edge straddles a threshold is computed from trivariate orthant probabilities (Sheppard's formula), and one random sample simultaneously controls every frontier. Saturated compression reduces subcubic graphs to cubic ones.

## Depends on

- [Layouts of multigraphs, cycle rank and the layout hypothesis](../frontier-method/layouts-and-the-layout-hypothesis.md)
- [Sheppard's formula (Gaussian arcsine law)](../../../Probability/distributions/continuous/multivariate-normal-distribution/sheppard-formula/sheppard-quadrant-probability-arcsine.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
