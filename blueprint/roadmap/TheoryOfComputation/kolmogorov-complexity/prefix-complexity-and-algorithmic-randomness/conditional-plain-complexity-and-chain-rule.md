# Conditional plain complexity and the chain rule

Here $C$ is plain Kolmogorov complexity, the complexity written $K$ on the linked Kolmogorov complexity page. The *conditional plain complexity* $C(y \mid x)$ is the length of a shortest program that outputs $y$ when given $x$ as auxiliary input, relative to a conditional universal method (invariance holds as for $C$). The *pair complexity* $C(x, y)$ is the complexity of a fixed computable encoding of the pair. The *algorithmic information* of $x$ about $y$ is $I(x : y) = C(y) - C(y \mid x)$. The easy direction of the chain rule is $C(x, y) \le C(x) + C(y \mid x) + 2\log_2(C(x)+1) + O(1)$, by concatenating a self-delimiting shortest program for $x$ with one for $y$ given $x$.

## Depends on

- [Kolmogorov complexity](../k.md)
- [Self-delimiting code for binary strings](self-delimiting-code-for-binary-strings.md)

## Sources

- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
