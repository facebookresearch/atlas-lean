# Distributed control of asynchronous automata with causal memory is undecidable

No algorithm decides whether the processes of an asynchronous automaton, each deciding from its causal view of the play, have a joint strategy that drives every process to a final state against all environment actions; this holds already for six processes.

**Asynchronous automata.** An *asynchronous automaton* over a finite set $\mathbb{P}$ of processes is a tuple $\mathcal{A} = ((A_p)_{p \in \mathbb{P}}, (Q_p)_{p \in \mathbb{P}}, (i_p)_{p \in \mathbb{P}}, (F_p)_{p \in \mathbb{P}}, \Delta)$, where each process $p$ has a finite set $A_p$ of actions, a finite set $Q_p$ of states, an initial state $i_p$ and a set $F_p \subseteq Q_p$ of final states. Let $A = \bigcup_p A_p$ and, for $a \in A$, $\mathrm{dom}(a) = \{p : a \in A_p\}$. The set $\Delta$ consists of transitions $(a, (q_p, q'_p)_{p \in \mathrm{dom}(a)})$ and is deterministic: for each $a$ and each tuple $(q_p)_{p \in \mathrm{dom}(a)}$ there is at most one such transition. Processing $a$ updates exactly the processes in $\mathrm{dom}(a)$, so letters with disjoint domains commute; *plays* are the traces (words up to this commutation) that the transitions allow from the initial states, and each play $u$ has a global state $(\mathrm{state}_p(u))_{p \in \mathbb{P}}$.

**Games and strategies.** A *distributed game* is an asynchronous automaton together with a partition $A = A_c \sqcup A_e$ into controllable and environment actions. The *causal view* $\mathrm{view}_p(u)$ of a play $u$ by process $p$ is the prefix such that $u = \mathrm{view}_p(u) \cdot v$ with $v$ the longest suffix in which $p$ does not take part. A *strategy for $p$* maps each play $u$ to a set $\sigma_p(u) \subseteq A$ of allowed actions with $A_e \subseteq \sigma_p(u)$ and $\sigma_p(u) = \sigma_p(\mathrm{view}_p(u))$. A play $a_1 \cdots a_n$ is consistent with a *distributed strategy* $\sigma = (\sigma_p)_{p \in \mathbb{P}}$ if $a_i \in \sigma_p(a_1 \cdots a_{i-1})$ for every $i$ and every $p \in \mathrm{dom}(a_i)$. The strategy is *winning* if the set of plays consistent with it is finite and every maximal such play $u$ satisfies $\mathrm{state}_p(u) \in F_p$ for all $p$.

**Theorem (Gimbert).** The *distributed control problem*, which asks whether a given distributed game has a winning distributed strategy, is undecidable, already for games with six processes (stated in the abstract; it follows from Theorems 2.4 and 3.1 of the source).

Four processes do not suffice for this construction: the distributed control problem is decidable for four processes, as the source recalls. The source notes that the construction adapts to deadlock-freeness winning conditions through the infinite version of the Post correspondence problem, and that the undecidability carries over to Petri games with a bounded number of tokens.

## Depends on

- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof passes through the *bipartite coloring problem*: given finite sets of colors and of initial, final, square and triangle patterns, decide whether some finite grid coloring $f \colon [n] \times [m] \to C$ realizes only allowed patterns. The Post correspondence problem reduces effectively to it, so it is undecidable. A second effective reduction turns an instance of the coloring problem into a six-process distributed game that has a winning strategy if and only if the instance has a solution: its six processes form a top pool and a bottom pool of three processes each, controllable increment actions synchronize neighboring processes of the same pool, and the game checks that the colors the processes choose form only allowed patterns.

## Sources

- H. Gimbert, "Distributed Asynchronous Games With Causal Memory are Undecidable", *Logical Methods in Computer Science* 18(3), 2022, article 30, doi:10.46298/lmcs-18(3:30)2022; read as arXiv:2110.14768v6, <https://arxiv.org/abs/2110.14768v6>: the abstract and conclusion (undecidability for six processes, deadlock-freeness), Theorem 2.4 (the Post correspondence problem reduces to the bipartite coloring problem), Theorem 3.1 (the bipartite coloring problem reduces to the distributed control problem with six processes), the definitions of asynchronous automata, causal views, distributed strategies and winning strategies in Section 1, and the introduction (four processes, Petri games), in the numbering of that version.
