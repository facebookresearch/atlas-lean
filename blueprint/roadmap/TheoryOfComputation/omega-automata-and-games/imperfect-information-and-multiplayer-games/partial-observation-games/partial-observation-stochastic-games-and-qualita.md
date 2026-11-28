# Partial-observation stochastic games and qualitative winning

In a two-player stochastic game of partial observation each player sees only which block of a partition of the states the
play is in; a strategy is observation-based if it depends only on what its player has seen, and it wins almost surely, or
positively, if it meets the objective with probability $1$, or with positive probability, against every opponent.

**Games.** A *concurrent game of partial observation* is a tuple $G = \langle S, A_1, A_2, \delta, \mathcal{O}_1, \mathcal{O}_2 \rangle$
with a finite set $S$ of states, finite action sets $A_1, A_2$, a probabilistic transition function
$\delta : S \times A_1 \times A_2 \to \mathcal{D}(S)$ with rational probabilities, and for $i = 1, 2$ a partition
$\mathcal{O}_i$ of $S$ into *observations*; $\mathrm{obs}_i(s)$ is the block containing $s$. Player $i$ has *complete
observation* if $\mathcal{O}_i$ consists of the singletons, and $G$ has *one-sided complete observation* if one of the players
does. A state is a *player-1 state* if the transition does not depend on the action of player $2$, a *player-2 state* if it does
not depend on that of player $1$; $G$ is *turn-based* if every state is one of these, and *deterministic* if every
$\delta(s, a, b)$ is a Dirac distribution. A game in which one action set is a singleton is a *partially observable Markov
decision process* (POMDP). A play is a sequence $s_0\, a_0 b_0\, s_1\, a_1 b_1 \cdots$ with
$\delta(s_j, a_j, b_j)(s_{j+1}) > 0$, and the observation sequence of player $1$ replaces each state by its observation and keeps
only the actions of player $1$.

**Strategies and winning.** A *randomized strategy* of player $1$ maps finite prefixes of plays to distributions on $A_1$; it
is *pure* if these are Dirac distributions, and *observation-based* if it gives the same value on any two prefixes with the
same observation sequence for player $1$; strategies of player $2$ are defined in the same way. A priority function
$p : S \to \{0, \dots, d\}$ defines the *parity* objective: the least priority seen infinitely often is even. The *Büchi* and
*coBüchi* objectives are the parity objectives with priorities in $\{0, 1\}$ and in $\{1, 2\}$; for a set $T$ of states,
$\mathrm{Buchi}(T)$ requires visiting $T$ infinitely often and $\mathrm{coBuchi}(T)$ requires staying in $T$ from some point
on. An objective is *visible* to player $i$ if any two plays with the same observation sequence for player $i$ both satisfy it
or both fail it. An observation-based strategy $\sigma$ of player $1$ is *almost-sure winning* for an objective $\varphi$ from
$s$ if $\Pr_s^{\sigma, \pi}(\varphi) = 1$ for every observation-based randomized strategy $\pi$ of player $2$, and *positive
winning* if $\Pr_s^{\sigma, \pi}(\varphi) > 0$ for every such $\pi$.

## Depends on

None.

## Proof depends on

None.

## Sources

- K. Chatterjee, L. Doyen, H. Gimbert and T. A. Henzinger, "Randomness for free", *Information and Computation* 245:3–16, 2015, doi:10.1016/j.ic.2015.06.003; conference version in *Mathematical Foundations of Computer Science 2010*, Lecture Notes in Computer Science 6281, pp. 246–257, Springer, 2010, doi:10.1007/978-3-642-15155-2_23. Section 2 of the version arXiv:1006.0673v3 (games of partial observation and their special cases, plays, observation-based strategies, parity, Büchi and coBüchi objectives, visibility, almost-sure and positive winning).
