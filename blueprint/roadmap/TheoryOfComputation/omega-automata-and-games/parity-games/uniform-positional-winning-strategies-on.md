# Uniform positional winning strategies on winning regions

Let $G$ be a parity game on a finite set of positions with the max-parity condition, in which every position has a move.

**Theorem.** The positions split into the winning regions $W_{\mathrm{Even}}$ and $W_{\mathrm{Odd}}$: every position lies in exactly one of them. Each player has a single positional strategy that wins every play starting anywhere in that player's winning region. Such a strategy keeps every consistent play inside the winning region.

This strengthens [positional determinacy from each position](finite-parity-games-are-positionally-determined.md), where the positional strategy may depend on the starting position, to one strategy per player.

**Proof.** For the min-parity condition this is memoryless determinacy as stated by Jurdziński: there is a unique partition $(W_\Diamond, W_\Box)$ of the positions with a winning strategy for each player from its whole set, a function $\sigma : V_\Diamond \to V$ and likewise for the opponent. Such a strategy is closed on the winning set. [Reversing priorities](min-parity-and-max-parity-games-have-the-same.md) transports the statement to the max-parity condition with the same strategies.

## Depends on

- [Finite parity games are positionally determined](finite-parity-games-are-positionally-determined.md)

## Proof depends on

- [Min-parity and max-parity games have the same winners after reversing priorities](min-parity-and-max-parity-games-have-the-same.md)

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *STACS 2000*, LNCS 1770, Springer, 2000, <https://www.dcs.warwick.ac.uk/people/academic/Marcin.Jurdzinski/Papers/Jur00-STACS.pdf>, Section 2: Theorem 1 (memoryless determinacy: a unique partition into winning sets with a winning strategy for each player from its set) and the characterization of winning strategies closed on a set.
- E. Grädel and I. Walukiewicz, "Positional determinacy of games with infinitely many priorities", *Logical Methods in Computer Science* 2(4:6), 2006, <https://arxiv.org/pdf/cs/0610035>, Introduction, item (3): parity games are positionally determined.
