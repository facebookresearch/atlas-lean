# First-order model checking in constant depth

Let $\varphi$ be a first-order sentence over a finite relational vocabulary. For every $n$ there is a Boolean formula over the unbounded fan-in basis whose inputs are the truth values of the atomic facts $R(a_1,\dots,a_\ell)$ of a structure with universe $\{1,\dots,n\}$, that evaluates to $1$ exactly on the structures satisfying $\varphi$; its depth is bounded by a constant depending only on $\varphi$ and its size is polynomial in $n$. Its size is $O(n^{k})$ for a sentence with $k$ quantifiers. Hence every property definable by a first-order sentence that may also use arbitrary fixed numerical relations on $\{1,\dots,n\}$ (whose atoms are hardwired as constants) is in nonuniform $\mathsf{AC}^0$.

## Proof sketch

Replace each universal quantifier by a conjunction over the $n$ elements and each existential quantifier by a disjunction; atomic formulas become input variables or constants.

## Depends on

- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)
- [The class $\mathsf{AC}^0$](../../../complexity-classes/time-and-space-complexity-classes/ac0.md)
- [Logics on finite structures as query languages](../../../descriptive-complexity/finite-model-theory/logics-on-finite-structures-as-query-languages.md)
- [Finite relational structures are determined by their atomic facts](../../../descriptive-complexity/finite-structures-and-definability/finite-structures-from-atomic-facts.md)

## Sources

- Neil Immerman, "Descriptive Complexity", Springer, 1999 (Chapter 5, first-order logic and $\mathsf{AC}^0$).
- David A. Mix Barrington, Neil Immerman, Howard Straubing, "On Uniformity within NC^1", Journal of Computer and System Sciences 41(3), 1990.
