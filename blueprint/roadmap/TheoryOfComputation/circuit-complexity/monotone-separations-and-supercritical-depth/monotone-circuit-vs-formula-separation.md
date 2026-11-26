# Exponential separation of monotone circuits and monotone formulas in monotone P

There is an explicit family of monotone functions $h_N$ on $N$ variables computable by monotone circuits of size $N^{O(1)}$ whose monotone formula size is $2^{N^{\Omega(1)}}$ (equivalently, whose monotone circuit depth is $N^{\Omega(1)}$). Such functions arise as CSP-satisfiability functions of lifted formulas with polynomial-size resolution refutations but large resolution depth.

## Proof sketch

Take an unsatisfiable formula $F$ with a polynomial-size resolution refutation whose tree-like refutations require exponential size (e.g. pebbling formulas). The CSP-SAT function of $F \circ g^n$ has small monotone circuits obtained from the dag-like refutation, while its monotone formula size is the size of a tree-like protocol for the lifted search problem, which by deterministic lifting is $2^{\Omega(\text{depth}\cdot\log m)}$.

## Depends on

- [Resolution refutation](../../../Logic/propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Composed functions, gadgets and lifting theorems](../../communication-complexity/randomized-and-dag-like-lifting/composed-function-lifting.md)

## Proof depends on

- [Garg–Göös–Kamath–Sokolov: dag-like lifting from resolution width](../../communication-complexity/randomized-and-dag-like-lifting/ggks-dag-lifting.md)
- [Raz–McKenzie: separation of the monotone NC hierarchy](raz-mckenzie-monotone-nc.md)

## Sources

- A. Garg, M. Göös, P. Kamath, D. Sokolov, "Monotone circuit lower bounds from resolution", STOC (2018); Theory of Computing 16 (2020).
- R. Raz, P. McKenzie, "Separation of the monotone NC hierarchy", Combinatorica 19 (1999) 403-435; FOCS (1997).
