# Kolmogorov–Levin symmetry of information for plain complexity

For all objects $x, y$, writing $k = C(x, y)$ for plain complexity (the complexity written $K$ on the Kolmogorov complexity page),

$$
C(x, y) = C(x) + C(y \mid x) + O(\log(k+2)),
$$

and consequently $|I(x : y) - I(y : x)| = O(\log(k+2))$: algorithmic information is symmetric up to logarithmic terms. (The term $\log(k+2)$ only keeps the bound meaningful for the finitely many pairs with $k \le 1$.)

## Proof sketch

The upper bound on $C(x,y)$ is the chain rule. For the lower bound, let $A = \{(x', y') : C(x', y') \le k\}$, enumerable given $k$, with $|A| < 2^{k+1}$, and let $A_x$ be its section at $x$; put $m = \lceil \log_2 |A_x| \rceil$. Given $x$, $k$ and $m$, $y$ is described by its $m$-bit index in $A_x$, so $C(y \mid x) \le m + O(\log(k+2))$. The set of $x'$ with $|A_{x'}| > 2^{m-1}$ has fewer than $2^{k-m+2}$ elements and is enumerable from $k$ and $m$, so $C(x) \le k - m + O(\log(k+2))$. Adding gives $C(x) + C(y \mid x) \le k + O(\log(k+2))$. Since $C(x,y) = C(y,x) + O(1)$, applying the equality to both orders gives the symmetry of $I$.

## Depends on

- [Conditional plain complexity and the chain rule](conditional-plain-complexity-and-chain-rule.md)

## Sources

- A. K. Zvonkin and L. A. Levin, "The Complexity of Finite Objects and the Development of the Concepts of Information and Randomness by Means of the Theory of Algorithms", Russian Mathematical Surveys 25(6), 83–124, 1970.
- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
