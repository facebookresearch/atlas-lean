# Solving Rabin games is NP-complete

Deciding whether Eve wins a given finite game with a [Rabin objective](muller-rabin-and-streett-objectives.md), given by its
arena, coloring and pairs, from a given vertex is NP-complete. A certificate is a positional winning strategy, which exists
by positional determinacy and can be checked in polynomial time; hardness is by a reduction from satisfiability of
formulas in conjunctive normal form.

## Depends on

- [Muller, Rabin and Streett objectives](muller-rabin-and-streett-objectives.md)

## Proof depends on

- [Rabin games are positionally determined for the Rabin player](rabin-games-are-positionally-determined.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 3 (N. Fijalkow and F. Horn, "Regular games"): Theorem 3.3 and its proof.
