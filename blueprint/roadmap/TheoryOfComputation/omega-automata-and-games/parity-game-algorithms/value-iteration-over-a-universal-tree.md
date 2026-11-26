# Value iteration over a universal tree solves parity games in quasi-linear space

Let $d$ be even, padding an odd maximal priority by an unused even one. For every $(n, d/2)$-[universal tree](universal-trees.md) $T$, the value iteration (lifting) algorithm over $T$ computes, for every
[parity game](../parity-games/parity-game.md) with $n$ vertices and priorities in $\{1, \dots, d\}$, the least progress measure with values in the
leaves of $T$ and a top element, and Eve wins from a vertex exactly when its value is not the top element. With the
[quasipolynomial universal trees](quasipolynomial-universal-trees.md) this solves parity games with $n \ge 2$ vertices and $m$ edges in time
$O\big(m \log n \log d \cdot n^{2.45 + \log_2(1 + (d/2 - 1)/\log_2 n)}\big)$, which is quasipolynomial in general and polynomial when
$d = O(\log n)$, and in quasi-linear space, $O(n \log n \cdot \log d)$ (Jurdziński and Lazić).

## Depends on

- [Universal trees](universal-trees.md)
- [Parity game](../parity-games/parity-game.md)

## Proof depends on

- [Progress measures over a universal tree characterize the winner](progress-measures-over-a-universal-tree.md)
- [Quasipolynomial universal trees](quasipolynomial-universal-trees.md)
- [Progress measures give winning strategies in parity games](../parity-games/progress-measures-give-winning-strategies-in.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Theorem 2.9 (generic value iteration), Theorem 2.6 (the complexity bound) and the complexity analysis in Section 2.5.
- M. Jurdziński and R. Lazić, "Succinct progress measures for solving parity games", *Proceedings of the 32nd IEEE LICS*, 2017, arXiv:1702.05051v3: Section 1 (the quasi-linear space bound), Theorem 5 (correctness of the lifting algorithm) and Theorem 7 (its complexity).
