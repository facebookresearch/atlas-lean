# Separating automata for parity games

A *parity graph* is a finite directed graph whose edges carry priorities in $\{1, \dots, d\}$; it *satisfies parity* from a vertex
if every infinite path from there satisfies the parity condition, that is, the largest priority occurring infinitely often is
even, equivalently if every cycle reachable from it has an even largest priority. An automaton $A$ reading infinite words
over $\{1, \dots, d\}$ is *$(n, d)$-separating* if

- for every parity graph $G$ with $n$ vertices and priorities in $\{1, \dots, d\}$ and every vertex $v$ from which $G$ satisfies
  parity, $A$ accepts the sequence of priorities of every infinite path from $v$, and
- every word accepted by $A$ satisfies the parity condition.

A *safety automaton* is a finite automaton on infinite words with a set of rejecting states, which accepts a word when some
infinite run never visits a rejecting state.

## Depends on

- [Parity winning condition of a player](../parity-games/wins.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.4, Definition 2.1 and the preceding definitions of parity graphs and of safety automata.
- W. Czerwiński, L. Daviaud, N. Fijalkow, M. Jurdziński, R. Lazić and P. Parys, "Universal trees grow inside separating automata: quasi-polynomial lower bounds for parity games", *Proceedings of the 30th ACM-SIAM SODA*, 2019, arXiv:1807.10546v2: Sections 3.2 and 3.3 (safety automata and separators).
