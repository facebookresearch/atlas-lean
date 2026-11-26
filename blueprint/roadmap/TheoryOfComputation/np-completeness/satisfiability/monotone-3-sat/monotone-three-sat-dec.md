# MONOTONE 3-SAT as a decision problem

The decision problem MONOTONE 3-SAT accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a pair
$(n, \varphi)$ of a natural number $n$ and a CNF formula $\varphi$ such that every clause of
$\varphi$ is a list of exactly three literals (repetitions allowed), every literal of $\varphi$
has a variable below $n$, the literals of each clause are all positive or all negative, and
some assignment of truth values to the variables $0, \dots, n-1$, with every other variable
false, satisfies $\varphi$. Bitstrings that do not decode are rejected.
