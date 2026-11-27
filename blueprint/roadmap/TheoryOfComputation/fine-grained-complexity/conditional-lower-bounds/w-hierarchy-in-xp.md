# The W-hierarchy lies in XP

Weighted Circuit Satisfiability (does a Boolean circuit $C$ with $n$ inputs have a satisfying input of Hamming weight exactly $k$?) is decidable in time $O(n^{k}\cdot|C|)$; hence it lies in $\mathsf{XP}$, the class of parameterized problems decidable in time $f(k)\cdot|x|^{g(k)}$ for computable $f,g$. Consequently $\mathsf{FPT}\subseteq\mathsf{W}[1]\subseteq\mathsf{W}[t]\subseteq\mathsf{XP}$ for every $t\ge1$, and Clique and Independent Set are in $\mathsf{XP}$.

## Proof sketch

Enumerate all $\binom{n}{k}\le n^{k}$ weight-$k$ inputs and evaluate the circuit on each. $\mathsf{XP}$ is closed under parameterized reductions, and each $\mathsf{W}[t]$ is the closure of a restriction of Weighted Circuit Satisfiability under them; an FPT problem reduces to any nontrivial problem by solving it inside the reduction.

## Depends on

- [The level $\mathrm{W}(t)$ of the W-hierarchy](../../complexity-classes/parameterized-complexity/wlevel.md)
- [Weighted circuit satisfiability with bounded weft and depth](../../complexity-classes/parameterized-complexity/weighted-circuit-sat.md)
- [Fixed-parameter tractable problems](../../complexity-classes/parameterized-complexity/fpt.md)
- [FPT-reductions](../../complexity-classes/parameterized-complexity/fptreduces.md)

## Proof depends on

- [Parameterized complexity: FPT and W(1)-completeness of Clique](../../complexity-classes/parameterized-complexity/parameterized-clique-w1-complete.md)

## Sources

- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015, Definitions 1.3 and 13.16 and the discussion of Weighted Circuit Satisfiability in Section 13.3.
