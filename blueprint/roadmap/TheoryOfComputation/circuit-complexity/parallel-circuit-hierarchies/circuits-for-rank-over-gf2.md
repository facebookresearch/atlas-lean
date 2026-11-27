# Polynomial-size circuits for the rank over GF(2)

For all $r,c$ there is a De Morgan circuit of size polynomial in $r$ and $c$ that, given the $rc$ entries of a matrix $A\in\mathbb{F}_2^{r\times c}$, outputs $\operatorname{rank}_{\mathbb{F}_2}A$ in binary (and, for any threshold $\tau$, decides $\operatorname{rank}A\ge\tau$).

## Proof sketch

Gaussian elimination over $\mathbb{F}_2$ is a fixed sequence of row operations controlled by pivot searches, each realizable by multiplexers and exclusive ors of polynomial size.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Alexander A. Razborov, Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences, 1997.
