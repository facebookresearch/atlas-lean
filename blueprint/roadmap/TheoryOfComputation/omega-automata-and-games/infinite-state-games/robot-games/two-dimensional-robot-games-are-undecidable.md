# Two-dimensional robot games are undecidable

In the two-player vector game in which Adam and Eve alternately add one of their finitely many integer vectors to a counter vector in $\mathbb Z^2$, it is undecidable whether Eve can force the zero vector, although the game in dimension one is EXPTIME-complete.

**Theorem.** A *robot game* in dimension $n$ consists of two finite sets $A, E \subseteq \mathbb Z^n$ of moves of Adam and of Eve and an initial vector $x_0 \in \mathbb Z^n$. A play proceeds in rounds from $x_0$: in each round Adam first adds a vector of $A$ to the current vector, then Eve adds a vector of $E$; Eve wins if after one of her turns the current vector is $0^n$. Eve has a winning strategy if she can reach the zero vector whatever Adam plays. There is no algorithm that decides, given a two-dimensional robot game $(A, E)$ and $x_0 \in \mathbb Z^2$, whether Eve has a winning strategy. The source states the result, in its appendix, for games in which Adam has $8$ moves and Eve has $2083$ moves, obtained from a universal two-counter machine with $32$ instructions (Corollary 15; its proof counts at most $2083$ moves for Eve).

As a consequence, deciding whether Eve wins a three-dimensional matrix game, in which both players multiply by integer $3 \times 3$ matrices, is undecidable (Theorem 16). Robot games in dimension one are EXPTIME-complete, as recalled in Section 1 of the source.

## Depends on

- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof first reduces reachability of a configuration with both counters zero in a deterministic two-counter machine to *robot games with states*, where Eve has a finite control and Adam is stateless and never modifies the second counter (Theorem 2 and Corollary 7). Eve's moves simulate the machine's instructions on the two counters together with flags encoded modulo small numbers; Adam can let the simulation continue with a $0$-move, or challenge an incorrect move or a positivity claim, and any incorrect move by Eve lets Adam avoid the origin forever (Lemmas 3 to 6). Eve's control states are then encoded into the counters themselves, giving a stateless two-dimensional robot game in which Eve has a winning strategy iff she has one in the game with states (Theorem 8). Counting the moves of the construction applied to Korec's universal two-counter machine gives the bounds $2083$ and $8$.

## Sources

- R. Niskanen, I. Potapov and J. Reichert, "Undecidability of Two-dimensional Robot Games", in *41st International Symposium on Mathematical Foundations of Computer Science (MFCS 2016)*, Leibniz International Proceedings in Informatics 58, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2016, article 73, doi:[10.4230/LIPIcs.MFCS.2016.73](https://doi.org/10.4230/LIPIcs.MFCS.2016.73); read as arXiv:1604.08779v1, whose numbering is used here: Section 2 (robot games and robot games with states), Theorem 1, Theorem 2 with Lemmas 3 to 6, Corollary 7, Theorem 8, Corollary 14, Corollary 15 and Theorem 16.
