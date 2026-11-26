# The W-hierarchy lies in XP

Weighted Circuit Satisfiability (does a Boolean circuit with $n$ inputs have a satisfying input of Hamming weight exactly $k$?) is decidable in time $2^{O(k)}\cdot L^{O(k)}$, hence lies in $\mathsf{XP}$. Consequently $\mathsf{FPT}\subseteq\mathsf{W}[1]\subseteq\mathsf{W}[t]\subseteq\mathsf{W}[\mathrm{P}]\subseteq\mathsf{XP}$ for every $t$, and Clique and Independent Set are in $\mathsf{XP}$. Moreover $\mathsf{W}[\mathrm{P}]=\mathsf{FPT}$ iff Weighted Circuit Satisfiability is fixed-parameter tractable.

## Proof sketch

Enumerate all $\binom{n}{k}\le n^{k}$ weight-$k$ inputs and evaluate the circuit on each; XP is closed under fpt-reductions.

## Depends on

- [The level $\mathrm{W}(t)$ of the W-hierarchy](../../complexity-classes/parameterized-complexity/wlevel.md)
- [Weighted circuit satisfiability with bounded weft and depth](../../complexity-classes/parameterized-complexity/weighted-circuit-sat.md)
- [Fixed-parameter tractable problems](../../complexity-classes/parameterized-complexity/fpt.md)
- [FPT-reductions](../../complexity-classes/parameterized-complexity/fptreduces.md)

## Proof depends on

- [Parameterized complexity: FPT and W(1)-completeness of Clique](../../complexity-classes/parameterized-complexity/parameterized-clique-w1-complete.md)

## Sources

- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015, Definition 13.16.
