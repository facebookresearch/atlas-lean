# Least fixed points of positive operators stabilize in polynomially many stages

Let $\varphi(R, \bar x)$ be a first-order formula with $R$ a $k$-ary relation variable occurring only positively. On a structure with $n$ elements the operator $F(R) = \{\bar a : \varphi(R, \bar a)\}$ is monotone, its least fixed point is the intersection of all pre-fixed points, and the stages $F^0(\emptyset) \subseteq F^1(\emptyset) \subseteq \dots$ reach it after at most $n^k$ iterations. Hence FO(LFP) queries are computable in polynomial time, and the formation rule (positivity of recursion variables, propagated through operators according to their variance) guarantees monotonicity syntactically.

## Proof sketch

Positivity gives monotonicity by induction on formulas; an increasing chain of subsets of the $n^k$ tuples stabilizes within $n^k$ steps; Knaster–Tarski identifies the limit with the least fixed point.

## Depends on

- [Formulas of first-order logic with least fixed points](../immerman-vardi-theorem/ogfo.md)
- [Positive occurrence of a relation symbol](../immerman-vardi-theorem/positive-in.md)

## Sources

- N. Immerman, "Relational Queries Computable in Polynomial Time", Information and Control 68(1–3), 86–104, 1986.
- N. Immerman, Descriptive Complexity, Springer, 1999.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
