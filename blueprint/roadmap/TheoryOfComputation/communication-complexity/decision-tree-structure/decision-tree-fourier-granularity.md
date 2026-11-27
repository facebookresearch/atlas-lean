# Integer-valued decision trees of depth k have Fourier coefficients in 2^{-k}ℤ

Let $T$ be a decision tree of depth $k$ with leaves labelled in a set $\beta$ and $g : \beta \to \mathbb{Z}$. Then every Fourier coefficient of $x \mapsto g(T(x))$ is an integer multiple of $2^{-k}$. If $f$ is Boolean of decision tree depth $k \ge 1$, read as $\pm 1$, its Fourier coefficients lie in $2^{1-k}\mathbb{Z}$, and they are integers for $k = 0$.

## Proof sketch

Every input follows exactly one consistent root-to-leaf path, so $g(T(x))=\sum_P g(\ell_P)\,\mathbf 1_{C_P}(x)$ over the consistent paths $P$, where $\ell_P$ is the leaf and $C_P$ the subcube fixed by the answers along $P$. A subcube of codimension $c\le k$ has indicator $\prod_{i}\frac{1\pm\chi_{\{i\}}}{2}$ over its $c$ fixed coordinates, whose coefficients are $\pm2^{-c}\in2^{-k}\mathbb Z$. For $\pm1$ values, write $f = 1 - 2\cdot\mathbf{1}_{f = -1}$ and apply the first statement to the $0/1$-valued tree computing $\mathbf 1_{f=-1}$.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014 (Fact 3.15 and Proposition 3.16, granularity of integer-valued decision trees).
