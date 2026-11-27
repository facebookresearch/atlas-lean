# Boolean circuits for multiplication in GF(2^n)

In the power basis of $\mathbb{F}_{2^n}=\mathbb{F}_2[X]/(m(X))$ for an irreducible polynomial $m$ of degree $n$, multiplication of two field elements is computed by a De Morgan circuit of size $O(n^2)$: form the $2n-1$ coefficients of the ordinary polynomial product with $n^2$ ANDs and XOR trees, then apply the fixed $\mathbb{F}_2$-linear reduction modulo $m$, whose matrix is hard-wired.

## Proof sketch

The product coefficient $c_k=\bigoplus_{i+j=k}a_ib_j$ costs $O(n)$ gates; reduction is a fixed linear map $\mathbb{F}_2^{2n-1}\to\mathbb{F}_2^n$ realized by XOR gates.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
