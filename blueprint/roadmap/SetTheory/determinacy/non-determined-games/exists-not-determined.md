# Existence of a non-determined game

If the set of moves `A` is countable and has at
least two elements, some payoff set `S ⊆ A^ℕ` is not determined. The proof diagonalises over
the continuum many strategies, each of which has continuum many plays (Gale and Stewart,
*Infinite games with perfect information*, Ann. of Math. Stud. 28 (1953); Moschovakis,
*Descriptive Set Theory*, 2nd ed., AMS 2009, Exercise 6A.6, stated there for `A = {0, 1}`).
It uses the axiom of choice, through a well-ordering of the strategies. With a single move [every set is determined](../gale-stewart-games/determined-of-subsingleton.md).

The proof well-orders the pairs (player, strategy) in order type at most `2^ℵ₀`. A strategy has at least `2^ℵ₀` plays: against it the opponent can spell out any binary sequence, using two distinct moves. At each stage, fewer than `2^ℵ₀` plays have been chosen, so two fresh plays of the current strategy can be put into and out of `S`. Then no strategy of player I wins, because one of its plays lies outside `S`, and no strategy of player II wins, because one of its plays lies in `S`. The countability of `A` keeps the number of strategies at most `2^ℵ₀`.

## Background

- [Existence of a Bernstein set](../../../Topology/descriptive-set-theory/bernstein-set-exists.md): the same diagonalisation, run against the uncountable closed subsets of the reals.
