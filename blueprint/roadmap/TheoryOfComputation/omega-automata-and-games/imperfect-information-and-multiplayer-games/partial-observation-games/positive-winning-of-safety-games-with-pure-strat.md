# Positive winning of safety games with pure strategies is undecidable under imperfect information

For concurrent stochastic games with imperfect information and pure observation-based strategies, no algorithm decides whether the first
player has a strategy that keeps the play safe with positive probability against every opponent, even when that player observes nothing.

Consider games and strategies as in [partial-observation stochastic games and qualitative winning](partial-observation-stochastic-games-and-qualita.md),
with both players restricted to *pure* observation-based strategies, and with players observing their own actions. For a set $F$ of states, the *safety* objective requires that no state
of $F$ is ever visited, and the *coBüchi* objective that states of $F$ are visited only finitely often. A pure strategy $\sigma$ of player $1$ (Eve) *positively wins* if every pure
observation-based strategy $\pi$ of player $2$ (Adam) gives the objective positive probability, and *almost-surely wins* if every such $\pi$ gives it probability $1$.

**Theorem.** For concurrent stochastic games with imperfect information, with pure observation-based strategies:

1. it is undecidable whether Eve positively wins a given safety game, and whether she positively wins a given coBüchi game, even when Eve observes nothing (all states look
   the same to her);

2. it is undecidable whether Eve almost-surely wins a given coBüchi game, and whether she positively wins a given Büchi game, even when Adam has a single action.

In contrast, the source shows that, for pure strategies, positive winning of reachability games is decidable when Adam is perfectly informed, and almost-sure winning of
Büchi games is decidable when Adam is perfectly informed or more informed than Eve.

## Depends on

- [Partial-observation stochastic games and qualitative winning](partial-observation-stochastic-games-and-qualita.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The value-1 problem for probabilistic automata is undecidable](../../../regular-languages/automata-and-expressions/weighted-automata-and-rational-series/value-1-problem-for-probabilistic-automata.md)

## Expansion

Item 2 is immediate from the undecidability of emptiness for probabilistic Büchi automata under the positive semantics and for probabilistic coBüchi automata under the almost-sure
semantics (Baier, Bertrand and Größer): a blind Eve playing alone chooses an infinite input word. For item 1, the proof combines a game built from a probabilistic automaton on finite
words, in which Eve plays a word and then a stop action, with the concurrent safety game Hide-or-Run, in which a hiding Adam must eventually run and Eve wins only with a correctly
timed throw. Eve positively wins the combined safety game exactly when the probabilistic automaton accepts words with probability arbitrarily close to $1$, so the value 1 problem
reduces to it.

## Sources

- A. Carayol, C. Löding and O. Serre, "Pure strategies in imperfect information stochastic games", *Fundamenta Informaticae* 160(4):361–384, 2018, doi:10.3233/FI-2018-1687; read in arXiv:1506.09140v2: Theorems 1 and 2 of Section 3 (Undecidability results) with their proofs and Lemma 1 (value 1), the definitions of Section 2, and Theorems 4 and 5 of Section 4 and Theorem 6 of Section 5 (the decidable cases), with the numbering of that version.
