# Qualitative Büchi and coBüchi objectives are undecidable in deterministic games with one-sided partial observation

No algorithm decides whether player $1$ has a randomized observation-based strategy that wins a coBüchi objective almost surely,
or a Büchi objective with positive probability, in a finite turn-based game with deterministic transitions in which only
player $1$ has partial observation.

Let $G$ range over finite turn-based [games of partial observation](partial-observation-stochastic-games-and-qualita.md) with
deterministic transition function and one-sided complete observation, with an initial state $s_*$ and a set $T$ of states (or a
union of observations).

**Theorem.** Both of the following problems are undecidable:

1. does player $1$ have a randomized observation-based strategy that is almost-sure winning from $s_*$ for $\mathrm{coBuchi}(T)$?
2. does player $1$ have a randomized observation-based strategy that is positive winning from $s_*$ for $\mathrm{Buchi}(T)$?

For pure strategies the corresponding problems are decidable, even for parity objectives: they are EXPTIME-complete. The source
first obtains the same undecidability for finite POMDPs, for pure and for randomized observation-based strategies, and states
that it holds even when the objective is visible to player $1$.

## Depends on

- [Partial-observation stochastic games and qualitative winning](partial-observation-stochastic-games-and-qualita.md)

## Proof depends on

None.

## Expansion

Baier, Bertrand and Größer proved that emptiness of probabilistic coBüchi automata under the almost-sure semantics, and of
probabilistic Büchi automata under the positive semantics, is undecidable. A probabilistic automaton is a POMDP whose controller
sees nothing but the letters it plays, so deciding whether a finite POMDP has a pure observation-based almost-sure winning
strategy for a coBüchi objective, or a positive winning one for a Büchi objective, is undecidable. In POMDPs randomized
observation-based strategies are no more powerful than pure ones for these questions, which extends the result to randomized
strategies. Finally, every game with probabilistic transitions and one-sided complete observation reduces, in a way that
preserves almost-sure and positive winning, to one with deterministic transitions: each probabilistic state becomes a state of
player $2$ followed by equiprobable successor states that player $1$ cannot tell apart, so that either player alone can
simulate the coin by playing uniformly at random.

## Sources

- K. Chatterjee, L. Doyen, H. Gimbert and T. A. Henzinger, "Randomness for free", *Information and Computation* 245:3–16, 2015, doi:10.1016/j.ic.2015.06.003; conference version in *Mathematical Foundations of Computer Science 2010*, Lecture Notes in Computer Science 6281, pp. 246–257, Springer, 2010, doi:10.1007/978-3-642-15155-2_23. Section 4 of the version arXiv:1006.0673v3: Corollary 2 and the paragraph before it, Corollary 1 (POMDPs) and the paragraph before it, and the reduction of Section 3.3 (probabilistic states simulated by one-sided complete-observation turn-based deterministic states).
