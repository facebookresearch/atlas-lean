# Gale–Stewart theorem

If the set of moves `A` is non-empty and `A^ℕ` carries the
product of the discrete topologies, every closed payoff set `S ⊆ A^ℕ` is determined
(Gale and Stewart, *Infinite games with perfect information*, Ann. of Math. Stud. 28 (1953);
Moschovakis, *Descriptive Set Theory*, 2nd ed., AMS 2009, Theorem 6A.2).

The proof is the non-losing-position argument of Gale and Stewart. Suppose player II has no winning strategy. If II does not win from a position where I is to move, I has a move after which II still does not win from any reply (Moschovakis, Lemma 6A.1, which picks II's winning strategies with the axiom of choice). Player I keeps choosing such moves. Every finite stage of the resulting play then extends to a play in `S`, because otherwise II could win by moving arbitrarily, so the play is a limit of points of `S` and lies in the closed set `S`. Both this theorem and the open case come from a single lemma about the player who wants an open set: either that player wins from the initial position, or the opponent can always move to a position from which the player still does not win, and then the play never enters a basic cylinder inside the open set.

## Background

- [Gale–Stewart theorem, open case](determined-of-is-open.md): the dual statement, obtained here from the same lemma.
- [Existence of a non-determined game](../non-determined-games/exists-not-determined.md): with two or more moves the theorem cannot be extended to all payoff sets.
