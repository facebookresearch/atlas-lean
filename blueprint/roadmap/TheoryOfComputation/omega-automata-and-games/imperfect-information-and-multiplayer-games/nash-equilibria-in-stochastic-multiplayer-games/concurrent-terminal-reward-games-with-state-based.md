# Concurrent terminal-reward games with state-based strategies

A concurrent terminal-reward game is a finite game graph where all players choose actions simultaneously and each sink state pays every player a reward; mixed strategies see only the sequence of visited states, not the actions played.

A *deterministic concurrent arena* is a tuple $\mathcal A=(S,\mathrm{Agt},\mathrm{Act},(\mathrm{Allow}_i)_{i\in\mathrm{Agt}},\mathrm{Tab})$ with finite sets $S$ of states, $\mathrm{Agt}$ of players and $\mathrm{Act}$ of actions, nonempty sets $\mathrm{Allow}_i(s)\subseteq\mathrm{Act}$ of actions available to player $i$ in $s$, and a transition function $\mathrm{Tab}:S\times\mathrm{Act}^{\mathrm{Agt}}\to S$ (in a stochastic arena $\mathrm{Tab}$ returns a distribution on $S$). A state $s$ is *final* if every action profile leads from $s$ back to $s$; $F$ is the set of final states. A *history* is a finite nonempty sequence of states that some sequence of action profiles realizes, a *run* is an infinite one, and a run is *terminating* if it visits $F$.

A *terminal-reward* function is given by $\nu:F\to\mathbb R$: a terminating run that reaches $f\in F$ has reward $\nu(f)$, and a non-terminating run has reward $0$. A *concurrent game with terminal-reward payoffs* is an arena with one terminal-reward function $\phi_i$ per player; in algorithmic questions the rewards are rational.

A *mixed strategy* of player $i$ is a map $\sigma_i:S^+\to\mathrm{Dist}(\mathrm{Act})$ with support in $\mathrm{Allow}_i(\mathrm{last}(h))$; it observes only the visited states, neither the actions nor the distributions chosen by the others. A profile $\sigma$ and an initial state $s_0$ determine a measure on runs, the players randomizing independently. The profile is a *Nash equilibrium from $s_0$* if for every player $i$ and every strategy $\sigma'_i$,

$$
\mathbb E^{\sigma[i/\sigma'_i]}(\phi_i\mid s_0)\le\mathbb E^{\sigma}(\phi_i\mid s_0).
$$

## Depends on

None.

## Proof depends on

None.

## Expansion

The model with invisible actions is more general than the one with visible actions. Nash equilibria need not exist with terminal rewards: a two-player zero-sum gadget has almost-optimal but no optimal strategies. With safety objectives for every player an equilibrium always exists.

## Sources

- Patricia Bouyer, Nicolas Markey and Daniel Stan, "Stochastic Equilibria under Imprecise Deviations in Terminal-Reward Concurrent Games", Electronic Proceedings in Theoretical Computer Science 226, 2016, pp. 61–75, doi:[10.4204/EPTCS.226.5](https://doi.org/10.4204/EPTCS.226.5); numbering of arXiv:1609.04089v1 ([arXiv](https://arxiv.org/abs/1609.04089v1)): Section 2, Definitions 1–4 (arenas, final states, terminal-reward functions, games, mixed strategies and Nash equilibria).
