# Relational second-order logic on finite structures

Second-order logic extends first-order logic over a relational vocabulary $\sigma$ by relation variables of specified arities and quantifiers $\exists R$, $\forall R$ ranging over all relations of that arity on the universe (full semantics). Element and relation quantifiers may nest in any order. *Existential second-order* (ESO) sentences have the form $\exists R_1 \cdots \exists R_m\, \varphi$ with $\varphi$ first-order over $\sigma \cup \{R_1,\dots,R_m\}$; $\mathfrak{A} \models \Phi$ iff some expansion of $\mathfrak{A}$ by relations $R_i$ satisfies $\varphi$. ESO-definable classes are closed under intersection, union and existential projection of further relation variables.

## Depends on

- [Satisfaction of an existential second-order sentence](../fagin-s-theorem/fagin-esosat.md)
- [Logics on finite structures as query languages](../finite-model-theory/logics-on-finite-structures-as-query-languages.md)

## Sources

- R. Fagin, "Generalized First-Order Spectra and Polynomial-Time Recognizable Sets", in Complexity of Computation, SIAM-AMS Proceedings 7, 43–73, 1974.
- N. Immerman, Descriptive Complexity, Springer, 1999.
