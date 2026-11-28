# Energy games on pushdown and two-dimensional one-counter arenas are undecidable

Energy games played on the configuration graph of a one-counter automaton are decidable with one energy dimension, but no algorithm decides them with two energy dimensions, nor on pushdown automata with a single energy dimension.

In a *pushdown energy game* of dimension $n$, control states are split between player 0 and player 1, a finite pushdown automaton determines the moves on configurations (state, stack), and each transition adds a vector in $\{-1,0,1\}^n$ to the current energy $E\in\mathbb Z^n$. The owner of the current configuration picks the next move; player 0 wins as soon as some energy component becomes negative, and player 1 wins every infinite play. A *one-counter energy game* is the special case where the stack is a counter that can be incremented, decremented and tested for zero. The energy components are not counters: they cannot be tested and never restrict the available moves (compare [mean-payoff and energy games](../mean-payoff-games-and-energy-games.md)). The *fixed initial credit problem* asks whether player 1 wins from a given configuration with a given initial energy; the *unknown initial credit problem* asks whether there is some initial energy from which player 1 wins.

**Theorem.** The fixed initial credit problem is undecidable for one-counter energy games of energy dimension $n\ge2$ (Theorem 13 of the source).

In Section V the source also shows that both the fixed and the unknown initial credit problems are undecidable for pushdown energy games, already for energy dimension $n=1$.

By contrast, for one-counter energy games of energy dimension $1$ the winning sets are semilinear and the fixed initial credit problem is decidable (Theorem 5). As a consequence of the correspondence between energy games and simulation games, simulation preorder between one-counter nets and vector addition systems of dimension $\ge2$, and between pushdown automata and one-counter nets, is undecidable.

## Depends on

- [Mean-payoff games and energy games are interreducible](../mean-payoff-games-and-energy-games.md)
- [Pushdown automaton](../../../context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)
- [One-counter automata and one-counter nets](../../../undecidable-problems/extended-finite-automata/regular-separability-of-one-counter-automata/one-counter-automata-and-one-counter-nets.md)
- [Arenas, strategies and memory structures](../../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Both items reduce halting of deterministic two-counter machines. For pushdown games, player 1 proposes the infinite run of the machine by pushing its transitions on the stack, and the single energy dimension lets player 0 challenge a step that is not a valid continuation and win exactly when player 1 has cheated; so player 0 wins from every initial credit iff the machine halts, and if player 0 wins from some credit she wins from all. For one-counter games, energy games and simulation games between one-counter automata and vector addition systems are interreducible, and the undecidability of simulation between one-counter nets and two-dimensional vector addition systems, proved from two-counter machines, transfers to two-dimensional energy.

## Sources

- Parosh Aziz Abdulla, Mohamed Faouzi Atig, Piotr Hofman, Richard Mayr, K. Narayan Kumar and Patrick Totzke, "Infinite-state energy games", in *Proceedings of the Joint Meeting of the 23rd EACSL Annual Conference on Computer Science Logic and the 29th Annual ACM/IEEE Symposium on Logic in Computer Science (CSL-LICS 2014)*, 2014, article 7, pp. 1–10, doi:[10.1145/2603088.2603100](https://doi.org/10.1145/2603088.2603100); read in arXiv:1405.0628v1 ([arXiv](https://arxiv.org/abs/1405.0628v1)), cited by section: the abstract, the preliminaries (pushdown energy games, one-counter automata and one-counter energy games), the summary of results, the section relating energy games and simulation games, and the section on undecidability results (the lemma for pushdown energy games and the theorem for one-counter energy games).
