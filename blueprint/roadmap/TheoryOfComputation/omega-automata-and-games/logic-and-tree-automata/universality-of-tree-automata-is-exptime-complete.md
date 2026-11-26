# Universality of nondeterministic tree automata is EXPTIME-complete

Deciding whether a given nondeterministic [bottom-up finite tree automaton](bottom-up-finite-tree-automata.md) over a ranked
alphabet $\mathcal{F}$ accepts every ground term over $\mathcal{F}$ is EXPTIME-complete. Membership follows by determinizing and
complementing; hardness is by simulating alternating linear-space Turing machines. Hence the exponential cost of
determinization cannot be avoided in general.

## Depends on

- [Bottom-up finite tree automata](bottom-up-finite-tree-automata.md)

## Proof depends on

- [Determinization, closure and decision properties of regular tree languages](determinization-closure-and-decision-properties.md)

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>: Theorem 1.7.7, the proof sketched there, and the remark before it on determinization.
