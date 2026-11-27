# One-terminal word equations with length constraints are NP-complete

If only one constant letter occurs in the equations, conjunctions and disjunctions of word equations together with linear length constraints have an NP-complete satisfiability problem, whatever the alphabet over which solutions are sought.

Let $A$ be a finite alphabet of constants, $a \in A$ one fixed letter, and $X$ a set of variables. Consider quantifier-free *positive* formulas built with $\wedge$ and $\vee$ from word equations $U = V$ with $U, V \in (X \cup \{a\})^*$, so that the same letter $a$ is the only constant occurring anywhere in the formula ($A$ may contain further letters), together with a set $\theta$ of linear length constraints, a system of linear equations with integer coefficients in the lengths $|x|$, written in binary. A solution is an assignment $h : X \to A^*$, empty words allowed, satisfying the formula and $\theta$. Deciding whether such a formula with length constraints has a solution in $A^*$ is NP-complete.

## Depends on

- [Word equations with length and regular constraints](length-and-regular-constraints.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [0-1 INTEGER PROGRAMMING FEASIBILITY is NP-complete](../../np-completeness/number-and-packing-problems/0-1-integer-programming/zero-one-ilp-np-complete.md)

## Expansion

*Reduction to arithmetic.* Any solution $h$ of an equation $U = V$ over $X \cup \{a\}$ satisfies the length equation $\sum_x |U|_x |h(x)| + |U|_a = \sum_x |V|_x |h(x)| + |V|_a$. Conversely, if natural numbers $\ell_x$ satisfy this linear equation, then $h(x) = a^{\ell_x}$ solves $U = V$, because both sides become powers of $a$ of the same length. Hence a conjunction of such equations together with $\theta$ is satisfiable exactly when the linear system formed by the length equations and $\theta$ has a solution in natural numbers, and every solution can be replaced by one using only the letter $a$ with the same lengths.

*Membership in NP.* A nondeterministic algorithm traverses the positive formula, choosing one disjunct at each $\vee$; the equations collected form one conjunction of the disjunctive normal form, without writing out that normal form, which may be exponentially large. It then needs a solution of the resulting linear system over $\mathbb N$. If such a system has a solution, it has one whose numbers have polynomially many bits (Papadimitriou's bound for integer linear programming), so the algorithm guesses it and checks it. This small-solution bound is a classical result without a page here.

*NP-hardness.* Reduce 0-1 integer programming feasibility. For an instance with variables $z_1, \dots, z_k$ and integer linear constraints, use string variables $x_j$ with $|x_j| = z_j$, impose $0 \le |x_j| \le 1$ by $|x_j| + |s_j| = 1$ with fresh slack variables $s_j$, and turn each inequality $\sum_j c_j z_j \le d$ into the equation $\sum_j c_j |x_j| + |t| = d$ with a fresh slack variable $t$. Together with the trivial equation $a = a$ this is an instance whose solutions correspond to feasible 0-1 points.

With negated equations allowed, one-terminal formulas with length constraints over a target alphabet with at least two letters are as hard as arbitrary word equations with length constraints. That is the companion page on negation.

## Sources

- Joel D. Day, Vijay Ganesh, Paul He, Florin Manea and Dirk Nowotka, "The Satisfiability of Word Equations: Decidable and Undecidable Theories", Reachability Problems (RP 2018), LNCS 11123, pp. 15–29, 2018, <https://doi.org/10.1007/978-3-030-00250-3_2>, Proposition 4 (statement) and Section 2 (linear length constraints as systems of linear Diophantine equations).
- Joel Day, Vijay Ganesh, Paul He, Florin Manea and Dirk Nowotka, "The Satisfiability of Extended Word Equations: The Boundary Between Decidability and Undecidability", arXiv:1802.00523v1, 2018 (extended version), Theorem 5.1 and its proof (the length equation, the reduction to linear Diophantine systems, NP membership via Papadimitriou's bound, and NP-hardness via integer linear programming). The hardness reduction above uses the 0-1 version and is written out here.
