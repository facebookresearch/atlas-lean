# Integer-valued decision trees of depth k have Fourier coefficients in 2^{-k}ℤ

Let $T$ be a decision tree of depth $k$ with leaves labelled in a set $\beta$ and $g : \beta \to \mathbb{Z}$. Then every Fourier coefficient of $x \mapsto g(T(x))$ is an integer multiple of $2^{-k}$. If $f$ is Boolean of decision tree depth $k \ge 1$, read as $\pm 1$, its Fourier coefficients lie in $2^{1-k}\mathbb{Z}$, and they are integers for $k = 0$.

## Proof sketch

The function has Fourier degree at most $k$ and integer values; a function of degree at most $k$ with integer values has coefficients in $2^{-k}\mathbb{Z}$ (via the Möbius/indicator expansion of its monomials over subcubes). For $\pm1$ values, writing $f = 1 - 2\cdot\mathbf{1}_{f = -1}$ improves the denominator by one factor of two.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [Functions computed by depth-d trees have Fourier degree at most d and total influence at most d](decision-tree-depth-bounds-fourier-degree.md)
- [Boolean functions of degree at most k have Fourier coefficients in 2^{1−k}ℤ](../../../Combinatorics/boolean-functions/fourier-expansion-supplements/granularity-of-low-degree-boolean-functions.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
