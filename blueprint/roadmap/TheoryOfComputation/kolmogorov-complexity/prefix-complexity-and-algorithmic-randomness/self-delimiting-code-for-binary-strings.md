# Self-delimiting code for binary strings

A *self-delimiting code* is an injective map $\bar{\cdot} : \{0,1\}^* \to \{0,1\}^*$ whose image is prefix-free, so that $\bar x y$ can be uniquely parsed into $x$ and $y$. A standard choice writes the binary representation of $|x|$ (the empty word when $|x| = 0$) with every bit doubled, then the separator $01$, then $x$, of length $|x| + 2\lceil \log_2(|x| + 1)\rceil + 2$. Self-delimiting codes encode pairs $\langle x, y \rangle = \bar x y$ and program headers.

## Depends on

- [Prefix-free code](../../../InformationTheory/source-coding/prefix-codes/is-prefix-free.md)

## Sources

- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
