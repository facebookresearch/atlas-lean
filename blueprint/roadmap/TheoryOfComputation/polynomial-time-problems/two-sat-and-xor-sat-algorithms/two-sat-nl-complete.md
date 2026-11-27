# 2-SAT is NL-complete

The set of satisfiable 2-CNF formulas is $\mathsf{NL}$-complete under logarithmic-space many-one reductions.

## Proof sketch

Unsatisfiability is in $\mathsf{NL}$: guess a variable $x$ and paths $x\leadsto\neg x\leadsto x$ in the implication graph; by Immerman–Szelepcsényi, 2-SAT itself is in $\mathsf{NL}$. Hardness: map $\langle G,s,t\rangle$ to the 2-CNF with clauses $\neg u\vee v$ for arcs $uv$, plus unit clauses $s$ and $\neg t$; it is unsatisfiable iff $t$ is reachable from $s$, and $\mathsf{NL}=\mathsf{coNL}$ turns this into hardness for 2-SAT.

## Depends on

- [2-SAT as a decision problem](../2-satisfiability/two-sat-dec.md)
- [The complexity class NL](../../complexity-classes/time-and-space-complexity-classes/nl.md)
- [Log-space many-one reductions](../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)

## Proof depends on

- [ST-connectivity is NL-complete](../../completeness-other-classes/directed-s-t-connectivity/stcon-nl-complete.md)
- [Immerman-Szelepcsenyi theorem: NL = coNL](../../complexity-classes/immerman-szelepcsenyi.md)

## Sources

- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Neil D. Jones, Y. Edmund Lien and William T. Laaser, "New Problems Complete for Nondeterministic Log Space", Mathematical Systems Theory 10, 1–17, 1976.
