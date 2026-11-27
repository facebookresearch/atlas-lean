# Lupanov's upper bound for De Morgan formulas

For every $\varepsilon>0$ there is $n_0$ such that for all $n\ge n_0$, every Boolean function $f:\{0,1\}^n\to\{0,1\}$ is computed by a De Morgan formula in negation normal form without constant leaves having at most $(1+\varepsilon)\,2^n/\log_2 n$ literal leaves.

## Proof sketch

Local coding adapted to formulas: partition a block of the variable cube into punctured radius-one spheres; on each sphere the restriction of $f$ is determined by few parameters, which are selected by small formulas and combined by disjunctions whose leaf counts add up to $(1+o(1))2^n/\log_2 n$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Lupanov's partition of a power-of-two cube into open spheres](lupanov-open-sphere-partition.md)

## Sources

- O. B. Lupanov, "On the Realization of Functions of Logical Algebra by Formulae of Finite Classes (Formulae of Limited Depth) in the Basis ∧, ∨, ¬", Problemy Kibernetiki, 1961.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
