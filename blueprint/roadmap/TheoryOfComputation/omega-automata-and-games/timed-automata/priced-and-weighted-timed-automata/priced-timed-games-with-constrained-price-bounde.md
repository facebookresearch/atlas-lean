# Priced timed games with constrained-price, bounded-time and repeated reachability objectives

A priced timed game is a two-player game on a timed automaton whose locations carry integer price rates and whose transitions
carry integer prices, possibly negative; objectives combine reaching a target with a constraint on the accumulated price.

**Arenas.** A *priced timed game* (PTG) is a tuple $\mathcal{A} = (L, C, I, \Sigma, \delta, \pi, G)$ where $L = L_1 \uplus L_2$ is a finite
set of locations partitioned between Player 1 and Player 2, $C$ is a finite set of clocks, $I$ assigns to each location an
invariant that is a clock zone (a convex set of valuations defined by constraints $c \bowtie i$ and $c - c' \bowtie i$ with
$i \in \mathbb{N}$), $\Sigma$ is a finite set of labels, $\delta : L \times \Sigma \to Z(C) \times 2^C \times L$ gives for each location and
label a guard zone, a set of clocks to reset and a successor, $\pi : L \cup \Sigma \to \mathbb{Z}$ is the price function and
$G \subseteq L$ is the set of target locations.

**Semantics.** Configurations are pairs $(\ell, \nu)$ with $\nu \in \mathbb{R}_{\ge 0}^C$ satisfying $I(\ell)$. In configuration
$(\ell, \nu)$, the player owning $\ell$ chooses a timed move $(t, a) \in \mathbb{R}_{\ge 0} \times \Sigma$ such that, for
$\delta(\ell, a) = (\zeta, R, \ell')$, the valuation $\nu + t$ satisfies the guard $\zeta$ and $\nu + t'$ satisfies $I(\ell)$ for all
$0 \le t' \le t$; the play moves to $(\ell', (\nu + t)[R := 0])$ and pays $\pi(\ell) \cdot t + \pi(a)$. A play is the resulting
infinite sequence; its price is the sum of the prices up to the first visit of a target location, and $+\infty$ if no target is
reached. A strategy of a player maps each finite play ending in one of
that player's locations to an available timed move. Player 1 aims to keep the price low and Player 2 the opposite; a strategy of Player 1 is winning if every play consistent with it
satisfies the objective.

**Objectives of Player 1.**

1. *Constrained-price reachability* $\mathrm{Reach}({\bowtie} K)$, for ${\bowtie} \in \{<, \le, =, \ge, >\}$ and $K \in \mathbb{N}$: reach
   a target with a price $p$ satisfying $p \bowtie K$.
2. *Bounded-time reachability* $\mathrm{TBReach}(K, T)$, for $K, T \in \mathbb{N}$: reach a target with price at most $K$ while the total
   elapsed time stays within $T$.
3. *Repeated reachability* $\mathrm{RReach}(\eta)$, for a nonnegative rational $\eta$ given as a fraction of integers (the source lets $\eta$ range over the nonnegative reals; a decision problem needs a finite input): in plays that continue forever, visit target locations infinitely
   often, each time with a payoff in $[-\eta, \eta]$.

PTGs refine [timed games](../timed-games.md): forgetting the prices leaves a timed reachability game.

## Depends on

- [Timed games](../timed-games.md)
- [Zones and difference-bound matrices](../zones-and-difference-bound-matrices.md)

## Proof depends on

None.

## Sources

- T. Brihaye, G. Geeraerts, S. N. Krishna, L. Manasa, B. Monmege and A. Trivedi, "Adding negative prices to priced timed games", in *CONCUR 2014 – Concurrency Theory*, Lecture Notes in Computer Science 8704, pp. 560–575, Springer, 2014, doi:10.1007/978-3-662-44584-6_38; Sections 2 and 3 of the version arXiv:1404.5894v6 (priced game graphs, plays, prices and strategies; the definition of priced timed games, their semantics and the three objectives).
