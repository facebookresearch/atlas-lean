# Deterministic top-down tree automata are strictly weaker

There is a recognizable set of ground terms that is not the language of any deterministic
[top-down tree automaton](top-down-tree-automata.md); hence deterministic top-down tree automata recognize strictly fewer
languages than nondeterministic top-down ones, and than deterministic bottom-up ones. An example is
$\{f(a, b), f(b, a)\}$ over $\{f, a, b\}$ with $f$ binary: a deterministic top-down automaton accepting both terms must assign
the same pair of states to the two arguments of the root in both, and so also accepts $f(a, a)$.

## Depends on

- [Top-down tree automata](top-down-tree-automata.md)

## Proof depends on

- [Determinization, closure and decision properties of regular tree languages](determinization-closure-and-decision-properties.md)

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>: Proposition 1.6.2 and its proof, and the discussion at the start of Section 1.6.
- F. Gécseg and M. Steinby, *Tree Automata*, Akadémiai Kiadó, Budapest, 1984; reissued with a preface to the second edition as arXiv:1509.06233, 2015, with the original numbering: Section 2.11, Theorem 2.11.6 (a recognizable forest is recognized by a deterministic root-to-frontier recognizer if and only if it is closed) and the introduction of Chapter 2.
