# The spectral norm of a decision tree is at most its number of leaves

Let $T$ be a decision tree with $L$ leaves and let $h(x) = g(T(x))$ with $g$ taking values in $[-1, 1]$. Then

$$\sum_{S} |\hat h(S)| \le L \le 2^{\mathrm{depth}(T)}.$$

Moreover a Boolean function computed by a tree of depth $d$, read as $\pm 1$, has at most $4^d$ nonzero Fourier coefficients.

## Proof sketch

Sum over reachable leaf subcubes rather than recursing on subtrees: the linked tree definition allows a variable to be tested again below its first test, and the subtree below a test of $x_i$ may still depend on $x_i$ (if the root tests $x$, its $0$-child computes $x$ and its $1$-child returns $0$, the tree computes $0$, but averaging the children's constant coefficients would give $1/4$). Every input follows exactly one consistent root-to-leaf path $P$, so $h=\sum_P g(\ell_P)\mathbf 1_{C_P}$ over the consistent paths, where $C_P$ is the subcube fixed by the answers along $P$. The indicator of a subcube of codimension $c$ has $2^c$ Fourier coefficients, each $\pm2^{-c}$, so its spectral norm is $1$; with $|g|\le1$ the spectral norm of $h$ is at most the number of consistent paths, at most $L$. For the count, a Boolean function of tree depth $d\ge1$ has coefficients in $2^{1-d}\mathbb Z$ and, by Parseval, squared coefficients summing to $1$, so at most $4^{d-1}\le4^d$ of them are nonzero; for $d=0$ there is one.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [Leaf counts of decision trees: depth and decision lists](leaf-counts-depth-rank-and-decision-lists.md)
- [Integer-valued decision trees of depth k have Fourier coefficients in 2^{-k}ℤ](decision-tree-fourier-granularity.md)

## Sources

- E. Kushilevitz and Y. Mansour, "Learning Decision Trees Using the Fourier Spectrum", SIAM Journal on Computing 22(6), 1993.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014 (Fact 3.15 and Proposition 3.16).
