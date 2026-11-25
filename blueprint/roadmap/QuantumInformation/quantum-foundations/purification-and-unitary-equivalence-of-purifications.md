# Purification and unitary equivalence of purifications

Let $\rho$ be a density operator on a finite-dimensional space $X$ and let $Y$ be a finite-dimensional space with
$\dim Y \ge \mathrm{rank}(\rho)$. Then there is a unit vector $u \in X \otimes Y$ with $\mathrm{Tr}_Y(uu^*) = \rho$. If
$u, v \in X \otimes Y$ are unit vectors with $\mathrm{Tr}_Y(uu^*) = \mathrm{Tr}_Y(vv^*)$, then $v = (I \otimes U)u$ for some unitary $U$ on
$Y$. Here $\mathrm{Tr}_Y$ is the partial trace over the second factor.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Finite-dimensional quantum state (pure and mixed).

## Depends on

- [Partial trace over the second factor](../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-right.md)

## Proof depends on

- [Schmidt decomposition](schmidt-decomposition.md)
- [Right partial trace of a rank-one matrix](../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-right-vec-mul-vec-star.md)

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Definition 2.9, Theorem 2.10 (a purification in $X \otimes Y$ exists if and only if $\dim(Y) \ge \mathrm{rank}(P)$) and Theorem 2.12 (unitary equivalence of purifications). <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
