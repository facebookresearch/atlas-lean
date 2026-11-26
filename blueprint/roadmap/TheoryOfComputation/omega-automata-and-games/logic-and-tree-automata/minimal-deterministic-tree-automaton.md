# The minimal deterministic tree automaton is unique

Every recognizable set $L$ of ground terms over a ranked alphabet has a complete deterministic
[bottom-up finite tree automaton](bottom-up-finite-tree-automata.md), with a transition for every symbol and every tuple of states, with the least
number of states among the complete deterministic automata recognizing $L$, and it is unique up to renaming of states: its states are the classes of the congruence $\equiv_L$, with transitions
$f([u_1], \dots, [u_n]) \to [f(u_1, \dots, u_n)]$ and final states the classes of the terms in $L$.

## Depends on

- [Bottom-up finite tree automata](bottom-up-finite-tree-automata.md)
- [Myhill–Nerode theorem for tree languages](myhill-nerode-theorem-for-tree-languages.md)

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>: Corollary 1.5.1 and its proof, and the automaton $A_{\min}$ in the proof of the Myhill–Nerode Theorem in Section 1.5.
- F. Gécseg and M. Steinby, *Tree Automata*, Akadémiai Kiadó, Budapest, 1984; reissued with a preface to the second edition as arXiv:1509.06233, 2015, with the original numbering: Section 2.6, Theorems 2.6.10, 2.6.11 and 2.6.13 (minimal tree recognizers, which are complete deterministic), and the paragraph after Theorem 2.7.1.
