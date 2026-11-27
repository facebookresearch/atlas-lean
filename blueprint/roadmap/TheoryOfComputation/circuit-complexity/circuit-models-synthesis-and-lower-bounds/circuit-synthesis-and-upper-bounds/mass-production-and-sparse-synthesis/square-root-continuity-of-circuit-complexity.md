# Square-root continuity of circuit complexity

For Boolean functions $\{0,1\}^n\to\{0,1\}^m$ let $\omega_{n,m}(r)$ be the largest value of $|C(f)-C(g)|$ over pairs $f,g$ that differ on at most $r$ inputs ($C$ = De Morgan circuit complexity). For $n=2p$, every $\varepsilon>0$ and all large $p$:

$$
\omega_{2p,1}(2^p)\le(1+\varepsilon)2^p,\qquad \omega_{2p,m}(2^p)\le(3+\varepsilon)2^p\ \text{ for } m\le 2p,
$$

and the order is optimal: $2^p\le 16\,\omega_{2p,1}(2^p)$ for all $p\ge 4$.

## Proof sketch

For one output, $g=f\oplus h$ where $h=f\oplus g$ has at most $2^p$ ones, so $C(g)\le C(f)+(1+\varepsilon)2^p$ by the sparse indicator bound and a constant number of gates for the XOR. For $m\le 2p$ outputs let $S$ (with $|S|\le 2^p$) be the set of inputs where $f$ and $g$ differ; compute $[x\in S]$ once with $(1+\varepsilon)2^p$ gates and, for each output $i$, a circuit agreeing on $S$ with the partial function $h_i|_S$ with $(1+\varepsilon)2^p/p$ gates; then $h_i=[x\in S]\wedge h_i$, and the $m\le 2p$ partial circuits cost at most $(2+2\varepsilon)2^p$. For the lower bound compare $f\equiv 0$ (complexity $1$) with the functions having exactly $2^p$ ones: there are at least $2^{p2^p}$ of them, while by the counting bound fewer than that many functions have complexity at most $2^{p-4}$ when $p\ge 4$, so some such $g$ has $C(g)\ge 2^{p-4}+1$. These bounds are derived here from the sparse synthesis bounds and counting; they are not stated in the source.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Sparse synthesis at the square root of the cube](sparse-synthesis-at-the-square-root.md)
- [Counting functions with small De Morgan circuits](../../circuit-models-and-classes/circuit-models-and-complexity-measures/counting-functions-with-small-circuits.md)

## Sources

- A. V. Chashkin, "On Computing Partial Boolean Functions", Matematicheskie Voprosy Kibernetiki 22, 152–222, 2024.
