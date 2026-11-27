# The Nisan–Wigderson generator for polynomials

Let $f$ be a polynomial in $m$ variables, $L$ a set of seed variables, and $S_1,\dots,S_n\subseteq L$ an $(m,a)$-*design*: $|S_i|=m$ and $|S_i\cap S_j|\le a$ for $i\neq j$, each with a fixed bijection to the variables of $f$. The *Nisan–Wigderson generator* is the polynomial map $\mathrm{NW}_f:F^{L}\to F^n$, $\mathrm{NW}_f(z)_i=f(z|_{S_i})$.

## Depends on

- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)
- [Nisan–Wigderson generator](../../pseudorandomness-and-one-way-functions/derandomization/nisanwigderson-generator.md)

## Sources

- Valentine Kabanets, Russell Impagliazzo, "Derandomizing Polynomial Identity Tests Means Proving Circuit Lower Bounds", Computational Complexity, 2004.
- Noam Nisan, Avi Wigderson, "Hardness vs Randomness", Journal of Computer and System Sciences, 1994.
