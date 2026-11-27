# History-constrained systems

A history-constrained system is a finite automaton each of whose transitions carries a guard language, and the transition may be taken only when the prefix read so far belongs to its guard.

A *history-constrained system* (HCS) is a tuple $A=(\Sigma,U,\mathcal G)$ where $\Sigma$ is a finite alphabet, $U$ is a labeled transition system over $\Sigma$ with transitions $T$, initial state and accepting states, and $\mathcal G=\{L_t\subseteq\Sigma^*: t\in T\}$ assigns a *guard* language to each transition. A sequence $(q_0,a_1,q_1,\dots,a_n,q_n)$ is a *run* if $q_0$ is initial and, for each $i$, $t=(q_{i-1},a_i,q_i)\in T$ and the prefix $a_1\cdots a_{i-1}$ lies in $L_t$. The word $a_1\cdots a_n$ is accepted if some run on it ends in an accepting state of $U$; $L(A)$ is the set of accepted words, and the *emptiness problem* asks whether $L(A)=\emptyset$. The system is deterministic if $U$ is.

The class X/Y consists of HCS whose underlying automaton is of type X and whose guards are given by automata of type Y; for instance DFA/DFA, NFA/DFA, DFA/PDA (pushdown guards) and DFA/Reach-1-DVASS, whose guards are deterministic one-dimensional vector addition systems with states (a nonnegative counter, no zero tests) accepting with the counter equal to $0$ in an accepting state.

## Depends on

None.

## Proof depends on

None.

## Expansion

With regular guards, an HCS still recognizes a regular language, but it can be exponentially more succinct than a finite automaton, and reachability games on NFA/DFA systems are EXPTIME-complete.

## Sources

- Louwe B. Kuijer, David Purser, Henry Sinclair-Banks and Patrick Totzke, "History-Constrained Systems", in *Formal Methods (FM 2026)*, Lecture Notes in Computer Science, 2026, pp. 541–558, doi:[10.1007/978-3-032-26204-2_28](https://doi.org/10.1007/978-3-032-26204-2_28); read in arXiv:2602.18143v2 ([arXiv](https://arxiv.org/abs/2602.18143v2)), cited by section: Section 2 (history-constrained systems, HCS specified with finite automata, emptiness), the definition of VASS in Section 6, and Sections 3–5 for the context.
