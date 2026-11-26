# Square-root continuity of circuit complexity

For Boolean functions $\{0,1\}^n\to\{0,1\}^m$ let $\omega_{n,m}(r)$ be the largest value of $|C(f)-C(g)|$ over pairs $f,g$ that differ on at most $r$ inputs ($C$ = De Morgan circuit complexity). For $n=2p$, every $\varepsilon>0$ and all large $p$:

$$
\omega_{2p,1}(2^p)\le(1+\varepsilon)2^p,\qquad \omega_{2p,m}(2^p)\le(3+\varepsilon)2^p\ \text{ for } m\le 2p,
$$

and the order is optimal: $2^p\le 16\,\omega_{2p,1}(2^p)$ for all $p\ge 4$.

## Proof sketch

A circuit for $g$ is obtained from one for $f$ by XOR-ing with $f\oplus g$, which is supported on at most $2^p$ points and is synthesized by the sparse synthesis bounds; for the lower bound, pick a set of $2^p$ points on which some function is hard by counting.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Sparse synthesis at the square root of the cube](sparse-synthesis-at-the-square-root.md)

## Sources

- A. V. Chashkin, "On Computing Partial Boolean Functions", Matematicheskie Voprosy Kibernetiki, 2024.
