# Attacker–Defender games on integer matrices of dimension four are undecidable

In two-player games where Defender and Attacker alternately apply their own integer matrices to a vector, or concatenate their own braids, no algorithm decides whether Attacker can force a return to the start; this holds for $4\times4$ matrices and for braids on three or five strands.

In an *Attacker–Defender game* two players move alternately from an initial position, Defender first in each round; Attacker wins if he can force reaching the target position, and Defender tries to prevent it.

**Theorem (Halava, Harju, Niskanen and Potapov).**
1. *Matrix games.* Given finite sets of matrices in $\mathbb Z^{4\times4}$ for Attacker and for Defender and an initial vector $x_0\in\mathbb Z^4$, where each move multiplies the current vector by a matrix of the moving player, it is undecidable whether Attacker has a strategy to return to $x_0$.
2. *Braid games.* Given finite sets of braids for Attacker and Defender and an initial braid, where each move concatenates a braid of the moving player, it is undecidable whether Attacker can reach a braid isotopic to the trivial braid, for braids in $B_3$ starting from a non-trivial braid and for braids in $B_5$ starting from the trivial braid.
3. *Word games.* It is undecidable whether Attacker wins the weighted word game over a binary free group alphabet (words concatenated in the free group, plus an integer counter; target: the empty word with counter $0$), and the word game on pairs of words, one over a binary and one over a unary group alphabet.

## Depends on

- [Braid group on n strands](../../../../GroupTheory/presentations-and-decision-problems/braid-and-artin/endomorphisms-of-braid-groups/braid-group.md)

## Proof depends on

- [Universality of integer weighted automata on infinite words is undecidable](../../weighted-and-counter-omega-automata/integer-weighted-automata-on-infinite-words/universality-of-integer-weighted-automata-on.md)

## Expansion

Defender supplies the letters of an infinite word one at a time and Attacker follows a run of an automaton with reverse acceptance; Attacker can force a zero-weight configuration iff the word is accepted, so Attacker wins iff the automaton is universal, which is undecidable. The run is encoded as a word game in a free group, with the counter as an integer; free group words embed injectively into $\mathbb Z^{2\times2}$ by the matrices $\left(\begin{smallmatrix}1&2\\0&1\end{smallmatrix}\right)$ and $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$, giving $4\times4$ matrices together with the counter, and into $B_3$ by $\sigma_1^4,\sigma_2^4$, with the counter carried by powers of the central braid $(\sigma_1\sigma_2\sigma_1)^2$. $B_5$ contains a direct product of two free groups of rank $2$, which carries the pair version of the word game.

## Sources

- Vesa Halava, Tero Harju, Reino Niskanen and Igor Potapov, "Weighted automata on infinite words in the context of Attacker–Defender games", *Information and Computation* 255, 2017, pp. 27–44, doi:[10.1016/j.ic.2017.05.001](https://doi.org/10.1016/j.ic.2017.05.001); read in arXiv:1411.4796v3 ([arXiv](https://arxiv.org/abs/1411.4796v3)), cited by section because its theorem counters are not recoverable: Section 4: the weighted word game theorem, the word game on pairs of group words, the matrix game theorem, the definition of braid groups and the braid game theorem, with the proofs in the appendices.
