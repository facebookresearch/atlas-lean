# Kane–Williams random restriction lemmas for linear threshold functions

Let $f$ be a linear threshold function on $n$ variables and let $\rho$ be a random restriction that leaves each variable alive with probability $p$ and fixes the others to uniform random bits. Then (gate version) $\Pr_\rho[f|_\rho\text{ is not constant}]=O(\sqrt p)$, and (wire version) the expected number of alive variables on which $f|_\rho$ depends is $O(p^{3/2}n)$. As a consequence, depth-two weighted threshold circuits computing Andreev's function on $n$ bits need $\Omega(n^{3/2}/\log^3 n)$ gates and $\Omega(n^{5/2}/\log^{7/2}n)$ wires.

## Proof sketch

A threshold function is forced to a constant unless the random partial sum of the fixed weights falls within a window of width comparable to the live weights; anti-concentration (Littlewood–Offord type estimates) bounds that probability. Applied to all bottom gates of a small circuit, most become constant under a restriction that keeps a copy of a hard function inside Andreev's function alive, and counting the few remaining threshold functions over the live variables contradicts the hardness of that copy.

## Depends on

- [Depth-two weighted threshold circuits](depth-two-weighted-threshold-circuits.md)
- [Andreev's function](../../circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/formula-size-lower-bounds/andreev-function.md)

## Proof depends on

- [Counting threshold functions over a feature family](counting-threshold-functions.md)

## Sources

- Daniel M. Kane, Ryan Williams, "Super-Linear Gate and Super-Quadratic Wire Lower Bounds for Depth-Two and Depth-Three Threshold Circuits", Proceedings of the Forty-Eighth Annual ACM Symposium on Theory of Computing (STOC 2016), 2016.
