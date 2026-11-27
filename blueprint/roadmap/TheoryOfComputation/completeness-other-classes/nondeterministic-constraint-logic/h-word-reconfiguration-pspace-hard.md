# Wrochna: H-word reconfiguration is PSPACE-hard for a fixed H

For a directed graph $H$ on a finite alphabet, an **$H$-word** is a word $w_1\cdots w_n$ with $(w_i,w_{i+1})\in E(H)$ for all $i$; a move changes one letter so that the result is again an $H$-word. There is a fixed finite digraph $H$ for which deciding whether one $H$-word can be transformed into another of the same length by moves is $\mathsf{PSPACE}$-complete (in particular $\mathsf{PSPACE}$-hard under polynomial-time many-one reductions); membership holds because a word of length $n$ is stored in $O(n)$ space and Savitch's theorem determinizes the search.

## Proof sketch

First build a fixed symmetric string rewriting system whose rules replace two letters by two letters (2-balanced) and whose word problem is $\mathsf{PSPACE}$-complete: words encode configurations of a fixed polynomial-space Turing machine accepting a $\mathsf{PSPACE}$-complete language, with the head and state written into the letter under the head, and each rule performs one local step; symmetry makes every rule reversible. Then encode words of this system as $H$-words over an alphabet with extra pair symbols, so that one rewriting step becomes a sequence of single-letter changes through $H$-words, and every sequence of single-letter changes between encodings decodes to a rewriting sequence.

## Depends on

- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Savitch's theorem: NPSPACE = PSPACE](../../complexity-classes/savitch.md)

## Sources

- Marcin Wrochna, "Reconfiguration in bounded bandwidth and tree-depth", Journal of Computer and System Sciences 93, 2018, Theorems 1 and 3 (numbering of arXiv:1405.0847).
