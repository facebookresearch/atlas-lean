# Canonical decision tree of a restricted DNF

Let $F = t_1 \vee \dots \vee t_s$ be a DNF and $\rho$ a restriction (a partial assignment of the variables). The *canonical decision tree* $\mathrm{CDT}(F|_\rho)$ is defined recursively: if $F|_\rho$ is constant, output it; otherwise let $t$ be the first term not falsified by $\rho$, query all free variables of $t$ in order, and on each answer $\sigma$ continue with the canonical tree of $F|_{\rho\sigma}$ (if $\sigma$ satisfies $t$, output $1$). It computes $F|_\rho$, and its depth bounds the decision tree complexity of $F|_\rho$.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Disjunctive normal form](../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/cnf-gadgets-and-encodings/disjunctive-normal-form.md)

## Sources

- J. Håstad, "Almost Optimal Lower Bounds for Small Depth Circuits", STOC 1986.
- A. A. Razborov, "Bounded Arithmetic and Lower Bounds in Boolean Complexity", in Feasible Mathematics II, Birkhäuser, 1995.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
