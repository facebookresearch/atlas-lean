# Distributed automata with schedulers and their classes

In the framework of Esparza and Reiter, a distributed automaton runs a finite-state agent on every node of a labeled graph, agents updating from the number of neighbors in each state as chosen by a scheduler, and the graph is accepted when all agents eventually agree on acceptance; combining four parameters gives seven classes of distinct power.

A *distributed machine* over a labeling alphabet $\Lambda$ with counting bound $\beta\ge1$ is a tuple $M=(Q,\delta_0,\delta,Y,N)$ with a finite set $Q$ of states, an initialization $\delta_0:\Lambda\to Q$, a transition function $\delta$ mapping a state and a neighborhood count $\mathcal N:Q\to\{0,\dots,\beta\}$ to a state, and disjoint sets $Y,N\subseteq Q$ of accepting and rejecting states. On a finite labeled graph $G=(V,E,\lambda)$, each node $v$ starts in $\delta_0(\lambda(v))$; in each step a *selection* $S\subseteq V$ is chosen and every $v\in S$ moves to $\delta(C(v),\mathcal N^C_v)$, where $\mathcal N^C_v(q)=\min(\#\text{neighbors of }v\text{ in state }q,\beta)$. A *schedule* selects every node infinitely often; a run *accepts* (*rejects*) if from some point on all agents are in $Y$ (in $N$). A *distributed automaton* is a machine with a *scheduler*, a selection constraint and a fairness constraint, such that on every graph either all fair runs accept or all reject.

Four parameters give classes $xyz$ (with selection): *detection* $\mathtt d$ ($\beta=1$) or $\mathtt D$ ($\beta>1$); *acceptance* $\mathtt a$ (halting: accepting and rejecting states are absorbing) or $\mathtt A$ (stable consensus); *selection* synchronous (written $\diamond$ here, the source's dollar sign: all nodes each step), liberal ($\mathtt s$, any set) or exclusive ($\mathtt S$, one node); *fairness* weak ($\mathtt f$) or strong ($\mathtt F$). With respect to expressive power these collapse into seven classes (Esparza and Reiter).

## Depends on

- [Finite simple graph](../../../../GraphTheory/planar-graphs-and-minors/graph-minors/fin-graph.md)

## Proof depends on

None.

## Expansion

These automata model weak distributed computing such as population-like protocols on graphs, with agents that cannot count beyond a bound and are scheduled adversarially; the synchronous distributed automata of Kuusisto and Reiter on directed graphs are a different model.

## Sources

- Flavio T. Principato, Javier Esparza and Philipp Czerner, "Undecidability of the emptiness problem for weak models of distributed computing", *Theoretical Computer Science* 1067, 2026, article 115757, doi:[10.1016/j.tcs.2026.115757](https://doi.org/10.1016/j.tcs.2026.115757); read in arXiv:2504.07339v1 ([arXiv](https://arxiv.org/abs/2504.07339v1)), whose numbering is used: the abstract, Section 2 (distributed machines, distributed automata and their classes, Proposition 1), Section 3 (Theorem 2, Lemma 3 and the overall argument), Section 4 (the classes with halting acceptance) and the conclusion.
