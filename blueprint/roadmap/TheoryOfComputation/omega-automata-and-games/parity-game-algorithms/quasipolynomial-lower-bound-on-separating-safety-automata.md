# Quasipolynomial lower bound on separating safety automata

Let $d$ be even, padding an odd maximal priority by an unused even one. Call a nondeterministic safety automaton over the priorities
$\{1, \dots, d\}$ a *strong $(n, d)$-separator* if it accepts every word that
encodes an infinite path in a parity graph with at most $n$ vertices and priorities in $\{1, \dots, d\}$ all of whose cycles have even
largest priority, and rejects every word whose largest priority occurring infinitely often is odd. Every strong
$(n, d)$-separator has at least

$$\binom{\lfloor \lg n \rfloor + d/2 - 1}{\lfloor \lg n \rfloor}$$

states, a quasipolynomial lower bound that nearly matches the known upper bounds, so polynomial-size strong safety separators
cannot be used to solve parity games in polynomial time by the reduction to safety games (Czerwiński, Daviaud, Fijalkow, Jurdziński,
Lazić and Parys). The corresponding question for separators of the even-cycle and odd-cycle languages is left open.

## Depends on

- [Separating automata for parity games](separating-automata-for-parity-games.md)

## Proof depends on

- [Separating automata and universal trees have the same size](separating-automata-and-universal-trees-have-the-same.md)
- [Quasipolynomial lower bound on universal trees](quasipolynomial-lower-bound-on-universal-trees.md)

## Sources

- W. Czerwiński, L. Daviaud, N. Fijalkow, M. Jurdziński, R. Lazić and P. Parys, "Universal trees grow inside separating automata: quasi-polynomial lower bounds for parity games", *Proceedings of the 30th ACM-SIAM SODA*, 2019, arXiv:1807.10546v2: Section 3.3 (separators and strong separators), Theorem 5.1 and the abstract.
