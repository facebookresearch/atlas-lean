# Generalized arc consistency of the extended global cardinality constraint is NP-hard

When each value may occur only a number of times drawn from an arbitrary given set, rather than an interval, the global cardinality constraint becomes NP-complete to satisfy, so enforcing generalized arc consistency on it is NP-hard.

**Extended GCC.** Let $X_1,\dots,X_n$ be distinct variables with finite domains contained in a fixed finite value set $D$ with $d=|D|$, and give each value $v\in D$ a finite set $K(v)\subseteq\mathbb N$, listed explicitly. The constraint allows the assignments in which, for every $v$, the number of variables taking $v$ lies in $K(v)$. In the occurrence-variable form it is $\mathrm{GCC}([X_1,\dots,X_n],[O_v]_{v\in D})$ with integer variables $O_v$ (the number of occurrences of $v$) whose domains are the sets $K(v)$; there GAC also prunes the $O_v$, so the two forms have the same solutions on the $X_i$ but different GAC outputs. With every $K(v)$ a fixed interval it is the [global cardinality constraint](global-cardinality-constraint.md).

**Theorem.**

1. Deciding whether an extended GCC has an allowed assignment (NoGACWipeOut) is NP-complete under polynomial-time many-one reductions, already when every $K(v)$ is either a two-element set $\{0,\deg(v)\}$ with $\deg(v)\ge1$ or an interval $[0,\deg(v)-1]$, where $\deg(v)$ is the number of variables whose domain contains $v$.
2. Consequently GACSupport and GACDomain on the extended GCC, in either form, are NP-hard under polynomial-time Turing reductions: unless P $=$ NP, no polynomial-time algorithm enforces GAC on the $X_i$, or on the $X_i$ and the $O_v$ together.

## Depends on

- [Global cardinality constraint and its value network](global-cardinality-constraint.md): the interval version being generalized.
- [Decision problems of generalized arc consistency](../gac-reasoning-problems.md): GACSupport and GACDomain.

## Proof depends on

- [3SAT is NP-complete](../../../np-completeness/satisfiability/3-satisfiability/sat3-dec-np-complete.md): the reduction starts from satisfiability of CNF formulas.
- [Intractability transfers between the GAC decision problems](../gac-intractability-transfer.md): NP-hardness of NoGACWipeOut gives NP-hardness of GACSupport and GACDomain.

## Expansion

Membership in NP is clear. For hardness, take a CNF formula with nonempty clauses $C_1,\dots,C_n$, clause $C_i$ having literal occurrences $C_{ij}$. The values are the literal values $x_k,\bar x_k$ and the clause values $C_i$, all distinct symbols, and the variables are tagged copies distinct from the values. Variables: one $x_k$ for each Boolean variable, with domain $\{x_k,\bar x_k\}$ (the two literal values), and one $C_{ij}$ for each literal occurrence, with domain {the literal value of $C_{ij}$, the clause value $C_i$}. Set $K(\ell)=\{0,\deg(\ell)\}$ for every literal value $\ell$ and $K(C_i)=[0,\deg(C_i)-1]$ for every clause value. A literal value is then taken either by nobody or by everybody who can take it; since $x_k$ takes $x_k$ or $\bar x_k$, exactly one of the two literal values of each variable is "true" and absorbs all its occurrences, the occurrences of false literals must take their clause value, and $K(C_i)$ forbids all occurrences of $C_i$ taking $C_i$, i.e. requires a true literal in each clause. Allowed assignments correspond one-to-one to satisfying truth assignments (Quimper et al., Lemma 11).

Bessiere, Hebrard, Hnich and Walsh quote the result in the occurrence-variable form, and prove a companion result: GAC on a GCC with fixed intervals becomes NP-hard as soon as variables may be repeated in $[X_1,\dots,X_n]$ (their Theorem 9). When the sets $K(v)$ are intervals $[l_v,u_v]$, Quimper et al. prune the count bounds: each lower bound is raised to the least number of occurrences of $v$ in an assignment of all $X_i$ respecting the upper bounds, all in $O(n^2d)$ steps (§4.1), and each upper bound is lowered to the largest number of occurrences of $v$ in an assignment respecting the lower bounds, by one unit-capacity flow computation per value, all in $O(d\,n^{2.66})$ steps (§4.2). This is bounds pruning of the counts, not domain consistency for arbitrary sets $K(v)$.

## Sources

- C.-G. Quimper, A. López-Ortiz, P. van Beek and A. Golynski, "Improved algorithms for the global cardinality constraint", *Principles and Practice of Constraint Programming – CP 2004*, Lecture Notes in Computer Science 3258 (2004), 542–556, doi:10.1007/978-3-540-30201-8_40. §7 (NP-completeness of extended-GCC), the reduction of Figure 1 and Lemma 11; author copy [https://cs.uwaterloo.ca/~vanbeek/Publications/cp04b.pdf](https://cs.uwaterloo.ca/~vanbeek/Publications/cp04b.pdf).
- C. Bessiere, E. Hebrard, B. Hnich and T. Walsh, "The complexity of reasoning with global constraints", *Constraints* 12(2) (2007), 239–259, doi:10.1007/s10601-006-9007-3. Theorem 7 (GCC with integer occurrence variables, attributed to Quimper et al.) and Theorem 9 (repeated variables), §4.4 of arXiv:0903.1139v1, [https://arxiv.org/abs/0903.1139v1](https://arxiv.org/abs/0903.1139v1).
