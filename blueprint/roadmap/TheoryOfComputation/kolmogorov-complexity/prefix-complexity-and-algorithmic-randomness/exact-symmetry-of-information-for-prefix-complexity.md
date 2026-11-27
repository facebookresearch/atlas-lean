# Exact symmetry of information for prefix complexity

For prefix complexity,

$$K(x, y) = K(x) + K\big(y \mid x, K(x)\big) + O(1),$$

equivalently $K(x, y) = K(x) + K(y \mid x^*) + O(1)$ with $x^*$ a shortest program for $x$. Hence $K(x) + K(y \mid x^*) = K(y) + K(x \mid y^*) + O(1)$, without the logarithmic loss of the plain version.

## Proof sketch

The upper bound concatenates $x^*$ with a prefix-free program for $y$ given $x^*$. For the lower bound, the function $x' \mapsto \sum_{y'} 2^{-K(x', y')}$ is lower semicomputable and bounded by $2^{-K(x') + O(1)}$ via the coding theorem; multiplying the section at $x$ by $2^{K(x) - c}$ for the constant $c$ of that bound gives a semimeasure on $y$ computable from $x$ and $K(x)$, and the conditional coding theorem converts it into $K(y \mid x, K(x)) \le K(x,y) - K(x) + O(1)$.

## Depends on

- [Prefix-free Kolmogorov complexity](prefix-free-kolmogorov-complexity.md)

## Proof depends on

- [Algorithmic probability and Levin's coding theorem](levin-coding-theorem.md)

## Sources

- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
- G. J. Chaitin, "A Theory of Program Size Formally Identical to Information Theory", Journal of the ACM 22(3), 329–340, 1975, Theorem 3.9(a), (c).
