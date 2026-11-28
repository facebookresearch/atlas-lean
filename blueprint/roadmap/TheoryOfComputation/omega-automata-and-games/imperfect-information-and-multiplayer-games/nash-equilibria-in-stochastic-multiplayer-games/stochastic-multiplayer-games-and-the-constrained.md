# Stochastic multiplayer games and the constrained Nash equilibrium problem

A stochastic multiplayer game is a finite graph game in which each vertex belongs to one player or to chance, and each
player wants to satisfy an $\omega$-regular objective; the problem NE asks for a Nash equilibrium whose payoff vector lies
between two given thresholds.

**Games.** Let $\Pi$ be a finite set of players. A *stochastic multiplayer game* (SMG) $\mathcal{G}$ has a finite set $V$ of
vertices, pairwise disjoint sets $V_i \subseteq V$ of vertices *controlled* by player $i \in \Pi$ (the remaining vertices are
*stochastic*), a set of edges in which every vertex has at least one successor, a rational probability distribution on the
successors of each stochastic vertex, a coloring $\chi : V \to C$ into a finite set of colors, and for each player $i$ an
objective $\mathrm{Win}_i \subseteq C^\omega$. As inputs, objectives are given in one of the standard finite forms over the colors: a parity condition (a priority for each color), a finite set of Streett or Rabin pairs $(F, G)$ of color sets, or a Muller condition (a family of accepting color sets); any $\omega$-regular objective reduces to these by a product with a deterministic word automaton (Section 2 of the source). The undecidability results already hold for terminal reachability objectives, given by the sets $F_i$. A *play* is an infinite path; player $i$ *wins* it if its sequence of colors
lies in $\mathrm{Win}_i$. An *initialised* SMG $(\mathcal{G}, v_0)$ fixes an initial vertex. A *terminal* vertex $v$ has itself
as its only successor. A *simple stochastic multiplayer game* (SSMG) is an SMG in which every vertex is colored by itself and
every objective is a *terminal reachability* objective: reach a given set $F_i$ of terminal vertices.

**Strategies.** A (randomized) *strategy* of player $i$ maps each history $x v$ with $v \in V_i$ to a probability distribution
on the successors of $v$; it is *pure* if every such distribution is a Dirac distribution. A *memory structure* is a triple
$(M, \delta, m_0)$ with update function $\delta : M \times V \to M$; a strategy with that memory chooses its distribution
from the current memory state and vertex, and it is *finite-state* if $M$ is finite. A *strategy profile*
$\vec{\sigma} = (\sigma_i)_{i \in \Pi}$ and $v_0$ determine a probability measure $\Pr^{\vec{\sigma}}_{v_0}$ on plays, and the
*payoff* of $\vec{\sigma}$ is the vector $(\Pr^{\vec{\sigma}}_{v_0}(\mathrm{Win}_i))_{i \in \Pi}$. The profile is a *Nash
equilibrium* if no player $i$ has a strategy $\tau$, of any kind, with
$\Pr^{(\vec{\sigma}_{-i}, \tau)}_{v_0}(\mathrm{Win}_i) > \Pr^{\vec{\sigma}}_{v_0}(\mathrm{Win}_i)$, where
$(\vec{\sigma}_{-i}, \tau)$ replaces $\sigma_i$ by $\tau$.

**Decision problems.** *NE* is the problem: given a finite initialised SMG $(\mathcal{G}, v_0)$ with rational transition
probabilities and $\omega$-regular objectives, and rational thresholds $\vec{x}, \vec{y} \in [0, 1]^\Pi$, is there a Nash
equilibrium of $(\mathcal{G}, v_0)$ with payoff at least $\vec{x}$ and at most $\vec{y}$, componentwise? *PureNE*, *FinNE* and
*PureFinNE* ask the same about Nash equilibria that are pure, finite-state, and pure finite-state profiles respectively. The
*qualitative* variant asks for a Nash equilibrium in which a distinguished player wins with probability $1$; it is the special
case $\vec{x} = (1, 0, \dots, 0)$, $\vec{y} = (1, \dots, 1)$.

Every finite SMG with $\omega$-regular objectives has a pure finite-state Nash equilibrium, so the difficulty of NE lies in
the constraint on the payoff. The two-player zero-sum case, in which one player has a reachability objective and the other
the complementary objective, is a [stochastic reachability game](../../quantitative-games/stochastic-arenas-and-games.md).

## Depends on

- [Arenas, strategies and memory structures](../../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)

## Proof depends on

None.

## Sources

- M. Ummels and D. Wojtczak, "The complexity of Nash equilibria in stochastic multiplayer games", *Logical Methods in Computer Science* 7(3), paper 20, 2011, doi:10.2168/LMCS-7(3:20)2011: Section 2.1 (SMGs), Section 2.2 (objectives, terminal reachability, SSMGs), Section 2.3 (strategies, the induced probability measure, strategies with memory), Section 3 (Nash equilibria and their existence) and the beginning of Section 4 (the problems NE, PureNE, FinNE, PureFinNE and the qualitative variant); numbering of the version arXiv:1109.4017v2.
