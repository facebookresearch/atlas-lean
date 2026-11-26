# First-order model checking in constant depth

Let $\varphi$ be a first-order sentence over a finite relational vocabulary. For every $n$ there is a Boolean formula over the unbounded fan-in basis whose inputs are the truth values of the atomic facts $R(a_1,\dots,a_\ell)$ of a structure with universe $\{1,\dots,n\}$, that evaluates to $1$ exactly on the structures satisfying $\varphi$; its depth is bounded by a constant depending only on $\varphi$ and its size is polynomial in $n$. Hence every first-order definable property (with arbitrary numerical predicates) is in nonuniform $\mathsf{AC}^0$.

## Proof sketch

Replace each universal quantifier by a conjunction over the $n$ elements and each existential quantifier by a disjunction; atomic formulas become input variables or constants.

## Depends on

- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)
- [The class $\mathsf{AC}^0$](../../../complexity-classes/time-and-space-complexity-classes/ac0.md)

## Sources

- Neil Immerman, "Descriptive Complexity", Springer, 1999.
- David A. Mix Barrington, Neil Immerman, Howard Straubing, "On Uniformity within NC^1", Journal of Computer and System Sciences, 1990.
