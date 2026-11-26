# Nondeterministic top-down and bottom-up tree automata recognize the same languages

A set of ground terms over a ranked alphabet is the language of a nondeterministic
[top-down tree automaton](top-down-tree-automata.md) if and only if it is recognizable, that is, the language of a
nondeterministic [bottom-up finite tree automaton](bottom-up-finite-tree-automata.md). The translation reverses the rules
$f(q_1(x_1), \dots, q_n(x_n)) \to q(f(x_1, \dots, x_n))$ and exchanges initial and final states.

## Depends on

- [Top-down tree automata](top-down-tree-automata.md)
- [Bottom-up finite tree automata](bottom-up-finite-tree-automata.md)

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>: Theorem 1.6.1 and the hint given for its proof.
- F. Gécseg and M. Steinby, *Tree Automata*, Akadémiai Kiadó, Budapest, 1984; reissued with a preface to the second edition as arXiv:1509.06233, 2015, with the original numbering: Section 2.2, Theorems 2.2.6 and 2.2.10.
