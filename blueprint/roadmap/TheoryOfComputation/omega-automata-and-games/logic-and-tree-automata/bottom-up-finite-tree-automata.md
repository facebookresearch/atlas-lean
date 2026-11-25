# Bottom-up finite tree automata

A *ranked alphabet* $\mathcal{F}$ is a finite set of function symbols, each with an arity $n \ge 0$, and $T(\mathcal{F})$ is the set of ground terms (finite trees) over $\mathcal{F}$. A nondeterministic finite tree automaton (NFTA) over $\mathcal{F}$ is a tuple $A = (Q, \mathcal{F}, Q_f, \Delta)$, where $Q$ is a finite set of states, $Q_f \subseteq Q$ is the set of final states and $\Delta$ is a finite set of transition rules $f(q_1, \dots, q_n) \to q$ with $f \in \mathcal{F}$ of arity $n$ and $q_1, \dots, q_n, q \in Q$.

A *run* of $A$ on a ground term $t$ is a map $r$ from the positions of $t$ to $Q$ such that, at every position $p$ labelled by a symbol $f$ of arity $n$, the rule $f(r(p1), \dots, r(pn)) \to r(p)$ is in $\Delta$. The run is successful if it assigns a final state to the root, and $t$ is accepted by $A$ if some run of $A$ on $t$ is successful. The language $L(A)$ is the set of accepted ground terms, and a set of ground terms is *recognizable*, or a regular tree language, if it is $L(A)$ for some NFTA $A$.

The automaton is *deterministic* (DFTA) if no two rules have the same left-hand side. A DFTA has at most one run on every ground term.

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>, Section 1.1: the definition of NFTA, runs, successful runs and recognizable languages, and of DFTA.
