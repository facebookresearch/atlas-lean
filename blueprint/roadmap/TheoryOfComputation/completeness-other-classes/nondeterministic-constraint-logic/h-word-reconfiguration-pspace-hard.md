# Wrochna: H-word reconfiguration is PSPACE-hard for a fixed H

For a directed graph $H$ on a finite alphabet, an **$H$-word** is a word $w_1\cdots w_n$ with $(w_i,w_{i+1})\in E(H)$ for all $i$; a move changes one letter so that the result is again an $H$-word. There is a fixed finite digraph $H$ for which deciding whether one $H$-word can be transformed into another of the same length by moves is $\mathsf{PSPACE}$-hard under polynomial-time many-one reductions.

## Proof sketch

Simulate a linear-space (single-tape) Turing machine: letters encode tape symbols together with head and state markers, and the edge relation of $H$ allows only local configurations consistent with the machine; symmetric string rewriting makes the simulation reversible, so reachability of the accepting word captures acceptance.

## Depends on

- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Sources

- Marcin Wrochna, "Reconfiguration in bounded bandwidth and tree-depth", Journal of Computer and System Sciences 93, 2018.
