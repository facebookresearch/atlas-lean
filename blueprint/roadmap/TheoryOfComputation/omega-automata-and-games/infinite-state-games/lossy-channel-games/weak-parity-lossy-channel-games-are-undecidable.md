# Weak parity games on lossy channel systems are undecidable

No algorithm decides who wins a two-player game on a lossy channel system with a weak parity, parity, Büchi or co-Büchi objective, already with perfect information when only the opponent may lose messages, while safety and reachability lossy channel games are decidable even under incomplete information.

A *lossy channel system* consists of finite automata (processes) communicating through finitely many unbounded FIFO channels over a finite message set; transitions test a channel for emptiness or its head letter and write a message, read one, or leave the channel unchanged, and in the *weak* transition relation any messages may additionally be lost. In a *lossy channel game* two players resolve the choices of the transitions on the configurations (control locations and channel contents); with *incomplete information*, player $\exists$ observes only the control location of one process and the heads of designated observable channels and must play observation-based strategies. A *weak parity* objective, given by priorities on observations, is won by a play whose minimal priority ever seen is even; for *parity*, the minimal priority seen infinitely often must be even.

**Theorem.** For lossy channel game structures with incomplete information, it is undecidable whether player $\exists$ has an observation-based winning strategy in a game with a visible weak parity objective (Proposition 3 and Theorem 1 of the source); as a consequence, games with parity objectives are undecidable as well.

The proof adapts the perfect-information result of Abdulla, Bouajjani and d'Orso: deciding whether player A wins a game on a lossy channel system with a weak parity objective is undecidable when only player B may lose messages (B-LCS games), and the same construction gives undecidability for Büchi and co-Büchi objectives. By contrast, games with visible safety or reachability objectives are decidable under incomplete information, and a finite-state observation-based winning strategy can be computed when one exists (Theorem 1).

## Depends on

- [Arenas, strategies and memory structures](../../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Abdulla, Bouajjani and d'Orso reduce the infinite computation problem for transition systems based on lossy channel systems, which is undecidable: player B simulates the system, losing messages as it likes, and player A follows passively. The source adapts this reduction to incomplete information by letting player $\exists$ play the role of A and the opponent the role of B; since A only follows the simulation and the priorities do not depend on channel contents, the incomplete information does not affect the argument.

## Sources

- Rayna Dimitrova and Bernd Finkbeiner, "Lossy Channel Games under Incomplete Information", in *Proceedings of the 1st International Workshop on Strategic Reasoning (SR 2013)*, Electronic Proceedings in Theoretical Computer Science 112, 2013, pp. 43–51, doi:[10.4204/EPTCS.112.9](https://doi.org/10.4204/EPTCS.112.9); read in arXiv:1303.0790v1 ([arXiv](https://arxiv.org/abs/1303.0790v1)): the definitions of partially specified lossy channel systems and LC-game structures with incomplete information (Definitions 1 and 2), the paragraph on parity objectives with Proposition 3 and its proof idea, and Theorem 1 (the summary theorem).
- The perfect-information undecidability is due to Parosh Aziz Abdulla, Ahmed Bouajjani and Julien d'Orso, "Monotonic and Downward Closed Games", *Journal of Logic and Computation* 18(1), 2008, pp. 153–169, doi:[10.1093/logcom/exm062](https://doi.org/10.1093/logcom/exm062), as recalled in the source above (not read).
