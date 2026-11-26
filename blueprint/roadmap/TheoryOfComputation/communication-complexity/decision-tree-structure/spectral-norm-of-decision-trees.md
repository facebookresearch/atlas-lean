# The spectral norm of a decision tree is at most its number of leaves

Let $T$ be a decision tree with $L$ leaves and let $h(x) = g(T(x))$ with $g$ taking values in $[-1, 1]$. Then

$$\sum_{S} |\hat h(S)| \le L \le 2^{\mathrm{depth}(T)}.$$

Moreover a Boolean function computed by a tree of depth $d$, read as $\pm 1$, has at most $4^d$ nonzero Fourier coefficients.

## Proof sketch

At a node querying $x_i$ with subtrees $h_0, h_1$, $\hat h(S) = \frac12(\hat h_0(S) + \hat h_1(S))$ for $i \notin S$ and similarly with the coefficient of $S \triangle \{i\}$ otherwise; since $S \mapsto S \triangle\{i\}$ is a bijection, the spectral norm of $h$ is at most the sum of those of the subtrees. Combined with granularity $2^{1-d}$ and Parseval, at most $4^{d}$ coefficients are nonzero.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [Leaf counts of decision trees: depth, rank and decision lists](leaf-counts-depth-rank-and-decision-lists.md)
- [Integer-valued decision trees of depth k have Fourier coefficients in 2^{-k}ℤ](decision-tree-fourier-granularity.md)

## Sources

- E. Kushilevitz and Y. Mansour, "Learning Decision Trees Using the Fourier Spectrum", SIAM Journal on Computing 22(6), 1993.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
