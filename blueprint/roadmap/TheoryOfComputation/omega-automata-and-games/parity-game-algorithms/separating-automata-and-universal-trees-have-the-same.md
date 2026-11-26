# Separating automata and universal trees have the same size

Let $d$ be even, padding an odd maximal priority by an unused even one. An $(n, d)$-[separating](separating-automata-for-parity-games.md) safety automaton yields an $(n, d/2)$-[universal tree](universal-trees.md)
with as many leaves as the automaton has states, and conversely an $(n, d/2)$-universal tree yields an $(n, d)$-separating deterministic
safety automaton with as many states as the tree has leaves. Every known quasipolynomial approach to solving parity games by
play summaries, progress measures or register games can be cast as a separating automaton, so this equivalence relates their
sizes (Czerwiński, Daviaud, Fijalkow, Jurdziński, Lazić and Parys).

## Depends on

- [Separating automata for parity games](separating-automata-for-parity-games.md)
- [Universal trees](universal-trees.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Theorem 2.10 and the remarks after it.
- W. Czerwiński, L. Daviaud, N. Fijalkow, M. Jurdziński, R. Lazić and P. Parys, "Universal trees grow inside separating automata: quasi-polynomial lower bounds for parity games", *Proceedings of the 30th ACM-SIAM SODA*, 2019, arXiv:1807.10546v2: Section 4 (Theorem 4.1 and the constructions of separators from universal trees) and Section 5 (universal trees inside separating automata).
