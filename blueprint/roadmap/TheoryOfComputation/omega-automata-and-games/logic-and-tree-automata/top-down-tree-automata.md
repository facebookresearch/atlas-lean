# Top-down tree automata

Let $\mathcal{F}$ be a ranked alphabet and $T(\mathcal{F})$ the set of ground terms over it, as for
[bottom-up finite tree automata](bottom-up-finite-tree-automata.md). A nondeterministic *top-down* finite tree automaton over
$\mathcal{F}$ is a tuple $A = (Q, \mathcal{F}, I, \Delta)$ of a finite set $Q$ of states, a set $I \subseteq Q$ of initial states
and a finite set $\Delta$ of rules $q(f(x_1, \dots, x_n)) \to f(q_1(x_1), \dots, q_n(x_n))$ with $n \ge 0$, $f \in \mathcal{F}$ of
arity $n$ and $q, q_1, \dots, q_n \in Q$ (for a constant $a$, a rule $q(a) \to a$). Starting at the root in a state, the
automaton rewrites downwards, assigning a state to every subterm; its language $L(A)$ is the set of ground terms $t$ such
that $q(t)$ rewrites to $t$ for some $q \in I$. The automaton is *deterministic* if it has exactly one initial state and no
two rules with the same left-hand side.

## Depends on

- [Bottom-up finite tree automata](bottom-up-finite-tree-automata.md)

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>: Section 1.6, the definition of top-down NFTAs and, in Proposition 1.6.2, of top-down DFTAs.
- F. Gécseg and M. Steinby, *Tree Automata*, Akadémiai Kiadó, Budapest, 1984; reissued with a preface to the second edition as arXiv:1509.06233, 2015, with the original numbering: Section 2.2, the nondeterministic root-to-frontier (NDR) recognizers, and Section 2.11 (deterministic root-to-frontier recognizers).
