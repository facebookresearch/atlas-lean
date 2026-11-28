# Concurrent limit-average games and their Nash equilibria

A concurrent limit-average game is a finite multiplayer game in which all players choose actions simultaneously, the joint
action determines the next state, and each player receives the limit-average of her state rewards; the problem NE asks for a
Nash equilibrium whose expected payoffs lie between two thresholds.

**Games.** A *concurrent game* has a finite nonempty set $\Pi$ of players, a finite nonempty set $S$ of states, for each player
$i$ and state $s$ a nonempty set $\Gamma_i(s)$ of actions from a finite set $\Gamma$, a deterministic transition function
$\delta : S \times \Gamma^\Pi \to S$, and for each player a reward function $r_i : S \to \mathbb{Q}$. A state is *controlled*
by player $i$ if every other player has a single action there, and the game is *turn-based* if every state is controlled by
some player. A play is a sequence $s_0 \vec{a}_0 s_1 \vec{a}_1 \cdots$ of states and legal action profiles with
$\delta(s_j, \vec{a}_j) = s_{j+1}$, and its *limit-average payoff* for player $i$ is

$$
\phi_i(\pi) = \liminf_{n \to \infty} \frac{1}{n} \sum_{j=0}^{n-1} r_i(s_j) .
$$

A state $s$ is *terminal* if $\delta(s, \vec{a}) = s$ for all legal $\vec{a}$. In a *terminal-reward game* nonzero rewards occur
only at terminal states, so a play that enters a terminal state $s$ pays $r_i(s)$ to player $i$ and a play that never does pays
$0$.

**Strategies and equilibria.** A *randomized strategy* of player $i$ maps every history ending in a state $s$ to a probability
distribution on $\Gamma_i(s)$, and it is *pure* if these distributions are degenerate. A strategy profile
$\vec{\sigma} = (\sigma_i)_{i \in \Pi}$ and an initial state $s_0$ determine a probability measure on plays, the players
randomizing independently, and the *payoff* of $\vec{\sigma}$ is the vector of expectations
$\mathbb{E}^{\vec{\sigma}}_{s_0}(\phi_i)$. The profile is a *Nash equilibrium* of $(\mathcal{G}, s_0)$ if no player can increase
her expected payoff by switching unilaterally to another strategy.

**Decision problem.** *NE* asks, given a concurrent game $\mathcal{G}$ with rational rewards, a state $s_0$ and thresholds
$\vec{x}, \vec{y} \in (\mathbb{Q} \cup \{\pm\infty\})^\Pi$, whether $(\mathcal{G}, s_0)$ has a Nash equilibrium with payoff at
least $\vec{x}$ and at most $\vec{y}$; *PureNE* asks the same for pure equilibria.

Turn-based games always have a Nash equilibrium, but concurrent games need not: a two-player terminal-reward game of de
Alfaro, Henzinger and Kupferman has none. The two-player zero-sum turn-based case without randomness is the
[mean-payoff game](../../quantitative-games/classical-quantitative-objectives.md).

## Depends on

None.

## Proof depends on

None.

## Sources

- M. Ummels and D. Wojtczak, "The complexity of Nash equilibria in limit-average games", in *CONCUR 2011 – Concurrency Theory*, Lecture Notes in Computer Science 6901, pp. 482–496, Springer, 2011, doi:10.1007/978-3-642-23217-6_32; Sections 1 to 3 of the version arXiv:1109.6220v1 (concurrent games, limit-average payoffs, terminal-reward games, strategies, the induced measure, Nash equilibria, the problem NE, and the example of a game without Nash equilibrium).
