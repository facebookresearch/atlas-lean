# Existence of Nash equilibria in three-player concurrent terminal-reward games is undecidable

Whether a deterministic concurrent game with three players and terminal-reward payoffs has a Nash equilibrium in mixed strategies that observe only the visited states is undecidable.

**Theorem.** The following problem is undecidable: given a deterministic [concurrent game with terminal-reward payoffs](concurrent-terminal-reward-games-with-state-based.md) with three players, rational rewards and an initial state $s_0$, does it have a Nash equilibrium from $s_0$ in mixed strategies, where strategies observe the sequence of visited states but not the actions played?

The threshold three is on the number of players and holds for the plain existence question, with no constraint on the payoffs. For pure strategies the existence problem is decidable in deterministic terminal-reward games, and the two-player case is open, even with rewards in $\{0,1\}$.

## Depends on

- [Concurrent terminal-reward games with state-based strategies](concurrent-terminal-reward-games-with-state-based.md)

## Proof depends on

None.

## Expansion

The result is due to Bouyer, Markey and Stan (2014), and the 2016 paper recalls it as the undecidability statement for its setting. Earlier, Ummels and Wojtczak showed undecidability for fourteen-player concurrent games in which actions are visible; hiding the actions brings the number of players down to three. A zero-sum gadget with no optimal strategy removes the need for a constraint that some player wins, which is why rewards of both signs are used; with nonnegative rewards the known undecidability needs that extra constraint. To circumvent undecidability, the 2016 paper relaxes Nash equilibria to equilibria under imprecise deviations, for which stationary equilibria always exist and one can be computed in polynomial space.

## Sources

- Patricia Bouyer, Nicolas Markey and Daniel Stan, "Stochastic Equilibria under Imprecise Deviations in Terminal-Reward Concurrent Games", Electronic Proceedings in Theoretical Computer Science 226, 2016, pp. 61–75, doi:[10.4204/EPTCS.226.5](https://doi.org/10.4204/EPTCS.226.5); numbering of arXiv:1609.04089v1 ([arXiv](https://arxiv.org/abs/1609.04089v1)): Theorem 1 (stated there as established, with attribution to the authors' FSTTCS 2014 paper) and the discussion before it in Section 2.3.
