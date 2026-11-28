# Emptiness of history-constrained systems with counter guards is undecidable

No algorithm decides whether a deterministic history-constrained system accepts some word when its guards are deterministic one-counter vector addition systems accepting with counter zero, nor when its guards are pushdown automata.

**Theorem (Kuijer, Purser, Sinclair-Banks and Totzke).** For [history-constrained systems](history-constrained-systems.md):
1. emptiness is undecidable for DFA[Reach-1-DVASS], deterministic systems whose guards are deterministic one-dimensional vector addition systems with reachability acceptance;
2. emptiness is undecidable for DFA[PDA], deterministic systems with pushdown guards.

By contrast, emptiness is decidable, and EXPSPACE-complete, for NFA[Cover-DVASS] systems, whose guards are deterministic vector addition systems of any dimension with coverability acceptance (only the control state matters).

## Depends on

- [History-constrained systems](history-constrained-systems.md)
- [The class EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Pushdown automaton](../../context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Disjointness of context-free languages is undecidable](../../undecidable-problems/undecidable-problems-for-context-free-grammars/exists-not-tm2-decidable-disjoint.md)
- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Item 1 reduces reachability in two-counter machines. The underlying DFA reads the sequence of counter actions $\mathtt{inc}_i,\mathtt{dec}_i,\mathtt{zero}_i$ and tracks the machine state; two one-state guards $G_1$, $G_2$ follow the two counters, each incrementing and decrementing on its own actions, and every $\mathtt{zero}_i$ transition is guarded by $G_i$, whose reachability acceptance means that counter $i$ is $0$ at that point. Two final zero tests, one per counter, lead to the only accepting state; they force both counters to be $0$ at the end and ensure that a decrement of a counter at $0$, which blocks its guard's run, cannot go undetected (Appendix D.1 of the source). Item 2 follows because an HCS with regular underlying automaton can recognize, up to an end marker, the intersection of the guard languages, and emptiness of the intersection of two context-free languages is undecidable. A good expansion links a page for the undecidability of halting of two-counter machines started with both counters at $0$, which follows from the linked universality theorem together with the undecidability of halting of Turing machines on the blank tape (the linked halting page states halting for codes on given inputs); reachability of $(q, (0,0))$ from $(p, (0,0))$ is that problem after adding a halting state.

## Sources

- Louwe B. Kuijer, David Purser, Henry Sinclair-Banks and Patrick Totzke, "History-Constrained Systems", in *Formal Methods (FM 2026)*, Lecture Notes in Computer Science, 2026, pp. 541–558, doi:[10.1007/978-3-032-26204-2_28](https://doi.org/10.1007/978-3-032-26204-2_28); read in arXiv:2602.18143v2 ([arXiv](https://arxiv.org/abs/2602.18143v2)), whose numbering is used: Corollary 2 (context-free guards) and Proposition 2 (computing intersections) in Section 3, and Theorems 3 and 4 (Reach-1-DVASS and Cover-DVASS guards) in Section 6, with the appendix proofs.
