# Piecewise-linear contraction fixpoints in any ℓp norm lie in UEOPL and are polynomial-time in fixed dimension

Let PL-CONTRACTION take a map $f:[0,1]^d\to[0,1]^d$ given by a linear arithmetic circuit (no product of two variables), purported to be contracting in the $\ell_p$ norm for a fixed $p\in\mathbb{N}\cup\{\infty\}$, and ask for its exact fixpoint, which is unique and rational when $f$ is contracting, or for a short certificate of non-contraction (a pair $x,y$ violating contraction, or a further certificate type produced by the reduction). Then PL-CONTRACTION lies in UEOPL under promise-preserving reductions. Moreover, for every fixed dimension $d$ and every $\ell_p$ norm, a fixpoint of a piecewise-linear contraction or a certificate is found in polynomial time (previously known only for $\ell_2$ and $\ell_\infty$), and for contraction maps given by general arithmetic circuits in fixed dimension, an approximate fixpoint or a certificate is found in polynomial time.

## Proof sketch

Discretise with grid widths chosen dimension by dimension, the width for coordinate $i$ depending on that for $i+1$, so that the direction functions of $f$ form a one-permutation discrete contraction map whose fixpoint rounds to the exact fixpoint. This is why only $i$-slices appear in OPDC. The fixed-dimension algorithms perform a nested binary search over slices that mirrors the OPDC line. Since the metric-given contraction problem BANACH is complete for CLS in dimension 3, the algorithms show that $\ell_p$ contraction in fixed dimension is unlikely to be CLS-complete.

## Depends on

- [UNIQUE-EOPL, the class UEOPL and PromiseUEOPL: one potential line certified by violation solutions](unique-eopl-and-ueopl.md)

## Proof depends on

- [OPDC lies in UEOPL under promise-preserving reductions via a surface-walking line with a lexicographic potential](opdc-in-ueopl.md)
- [CLS = PPAD ∩ PLS, with 2D-CLS, promise-CLS and Linear-CLS equal to CLS and Banach-type contraction problems complete](../continuous-local-search-and-gradient-descent/cls-equals-ppad-cap-pls.md)
- [One-Permutation Discrete Contraction (OPDC): direction functions on a grid with unique fixpoints on i-slices](one-permutation-discrete-contraction.md)

## Sources

- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", ICALP (2019), arXiv:1811.03841.
