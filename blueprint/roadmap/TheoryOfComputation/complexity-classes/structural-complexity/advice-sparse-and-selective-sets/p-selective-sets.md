# P-selective sets

A set $A\subseteq\{0,1\}^*$ is **P-selective** if there is a polynomial-time function $f$ (a *selector*) with $f(x,y)\in\{x,y\}$ such that whenever $x\in A$ or $y\in A$, also $f(x,y)\in A$. The **left cut** of an infinite binary sequence $r$ is $L(r)=\{x : 0.x\le 0.r_1r_2\cdots\}$ (lexicographic comparison with the prefix of $r$ of length $|x|$); every left cut is P-selective (select the lexicographically smaller string) and distinct sequences give distinct left cuts, so there are uncountably many P-selective sets.

## Depends on

- [Polynomial-time computable functions](../../the-classes-p-np-and-conp/is-poly-time.md)

## Sources

- Alan L. Selman, "P-Selective Sets, Tally Languages, and the Behavior of Polynomial Time Reducibilities on NP", Mathematical Systems Theory 13(1), 1979.
- Lane A. Hemaspaandra and Leen Torenvliet, "Theory of Semi-Feasible Algorithms", Springer, 2003.
