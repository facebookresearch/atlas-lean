# Permutation branching programs of bounded width

Let $G$ be a group (for width $w$, the symmetric group $S_w$). A *$G$-program* of length $\ell$ on $n$ Boolean inputs is a sequence of instructions $(i_t,a_t,b_t)$, $t=1,\dots,\ell$, with $i_t\in\{1,\dots,n\}$ and $a_t,b_t\in G$; on input $x$ it yields the product $\prod_{t=1}^{\ell}(x_{i_t}?\,a_t:b_t)\in G$. It *$\sigma$-computes* $f$ if the product equals $\sigma\neq e$ when $f(x)=1$ and equals $e$ when $f(x)=0$. A width-$w$ permutation branching program is an $S_w$-program; languages with polynomial-length programs and a length-dependent accepting set form the class of bounded-width branching programs.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- David A. Barrington, "Bounded-width polynomial-size branching programs recognize exactly those languages in NC^1", Journal of Computer and System Sciences, 1989.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
