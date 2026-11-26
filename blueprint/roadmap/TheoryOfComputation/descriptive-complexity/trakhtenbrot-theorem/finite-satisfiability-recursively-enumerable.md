# Finite satisfiability is recursively enumerable

The set of (codes of) first-order sentences that are finitely satisfiable is recursively enumerable, and the set of finitely valid sentences is co-recursively enumerable. Indeed $\varphi$ is finitely satisfiable iff there is $n$ such that $\varphi$ is satisfiable on $\{0,\dots,n\}$, and the latter relation is primitive recursive.

## Proof sketch

Enumerate $n = 0, 1, 2, \dots$ and run the primitive recursive fixed-size check; satisfaction depends only on the ground atoms over the symbols of $\varphi$ and on boundedly many variables.

## Depends on

- [Finite satisfiability and finite validity](finite-satisfiability-and-validity.md)
- [Multi-stack recognizable predicates are exactly the r.e. predicates](../../computability/decidable-and-recognizable-predicates/tm2-recognizable-iff-re-pred.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
