# A quasipolynomial attractor decomposition algorithm

There is a variant of the recursive attractor algorithm of McNaughton and Zielonka that solves every finite
[parity game](../parity-games/parity-game.md) with $n$ vertices in time $n^{O(\log n)}$ (Parys). The exponential algorithm repeatedly removes from the game
a dominion of the opponent found by a recursive call; these dominions are disjoint, so at most one of them contains more
than half of the vertices. The variant searches for dominions of bounded size and halves the bound in all but one recursive
call, which keeps the recursion tree quasipolynomial.

## Depends on

- [Parity game](../parity-games/parity-game.md)
- [Winning region of a parity game](../parity-games/winning-region.md)

## Proof depends on

- [Attractor](../parity-games/attractor.md)
- [Winning regions are traps for the opponent](../parity-games/is-trap-winning-region.md)

## Expansion

This page becomes ready once:

- Correctness of the recursive attractor algorithm of McNaughton and Zielonka for finite parity games (proof prerequisite; not yet stated)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Theorem 2.2, Algorithm 2.3 and Lemma 2.3 (correctness), and the discussion of dominions in Section 2.2; the bibliographic references of Chapter 2 credit the algorithm to Parys.
