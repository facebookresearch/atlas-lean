# Kolmogorov–Levin symmetry of information for plain complexity

For all objects $x, y$, writing $k = C(x, y)$:

$$C(x) + C(y \mid x) \le k + 2\log_2 k + 4\log_2\log_2 k + O(1), \qquad \big|C(x, y) - C(x) - C(y \mid x)\big| \le 6\log_2 k + O(1),$$

and consequently $|I(x : y) - I(y : x)| \le 12 \log_2 k + O(1)$: algorithmic information is symmetric up to logarithmic terms.

## Proof sketch

The upper bound on $C(x,y)$ is the chain rule. For the lower bound, let $A = \{(x', y') : C(x', y') \le k\}$ (enumerable given $k$) and $A_x$ its section at $x$, of size $2^{m}$. Given $x$, $k$ and $m$, $y$ is described by its index in $A_x$, so $C(y \mid x) \lesssim m$. The set of $x'$ whose sections have size at least $2^m$ has at most $2^{k - m + 1}$ elements and is enumerable from $k, m$, so $C(x) \lesssim k - m$; adding gives the claim with the logarithmic overheads for $k$ and $m$.

## Depends on

- [Conditional plain complexity and the chain rule](conditional-plain-complexity-and-chain-rule.md)

## Sources

- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
