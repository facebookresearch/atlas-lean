# Prefix-free Kolmogorov complexity

A description method $M$ (a partial computable map from binary programs to objects) is *prefix-free* if its halting set $\mathrm{dom}(M)$ is a prefix-free set. There is a universal prefix-free method $U$: for every prefix-free partial computable $M$ there is $c_M$ with $K_U(x) \le K_M(x) + c_M$ for all $x$, where $K_M(x) = \min\{|p| : M(p) = x\}$. The *prefix(-free) Kolmogorov complexity* is $K(x) = K_U(x)$. It satisfies $C(x) \le K(x) + O(1)$ and $K(x) \le C(x) + 2\log_2(C(x)+1) + O(1)$, where $C$ is plain complexity (the complexity written $K$ on the linked Kolmogorov complexity page; on this and the neighbouring pages $K$ denotes prefix complexity). Conditional prefix complexity $K(y \mid x)$ uses a uniformly prefix-free family indexed by the condition.

## Depends on

- [Kolmogorov complexity](../k.md)
- [Prefix-free code](../../../InformationTheory/source-coding/prefix-codes/is-prefix-free.md)

## Sources

- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- A. Shen, V. A. Uspensky and N. Vereshchagin, "Kolmogorov Complexity and Algorithmic Randomness", American Mathematical Society, 2017.
- G. J. Chaitin, "A Theory of Program Size Formally Identical to Information Theory", Journal of the ACM 22(3), 329–340, 1975.
