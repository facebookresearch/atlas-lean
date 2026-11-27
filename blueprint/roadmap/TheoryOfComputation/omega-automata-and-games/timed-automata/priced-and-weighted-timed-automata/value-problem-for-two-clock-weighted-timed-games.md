# The value problem for two-clock weighted timed games is undecidable

No algorithm decides, given a weighted timed game with two clocks, a starting location and a rational threshold $c$, whether the value of the game is at most $c$; this holds already with non-negative weights.

Weighted timed games, their plays, strategies and value $\mathsf{Val}_{\mathcal{G}}(\ell, \nu)$ are as in [weighted timed games](weighted-timed-games.md), here without final weights (all equal to $0$), so a play has the accumulated weight of its moves if it reaches a goal location and weight $+\infty$ otherwise. A game is *turn-based* when each location belongs to one player, and *time-bounded* when every play lasts at most a fixed amount of time.

**Theorem (Guilmant, Ouaknine and Vialard).** The *value problem*, which asks, given a weighted timed game, a starting location $\ell_0$ and a rational threshold $c$, whether $\mathsf{Val}_{\mathcal{G}}(\ell_0, \mathbf{0}) \le c$, is undecidable for two-player, turn-based, time-bounded weighted timed games with two clocks and non-negative integer weights (Theorem 1 of arXiv:2507.10550v2). The same holds for games over unbounded time that satisfy the other hypotheses.

The value problem is decidable for one-clock weighted timed games, and it was known to be undecidable from three clocks on (Bouyer, Jaziri and Markey), as the source recalls. The extended version of the paper also shows that the value of almost divergent turn-based two-clock weighted timed games is computable in triply exponential time.

## Depends on

- [Weighted timed games](weighted-timed-games.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from the halting problem for deterministic two-counter machines, undecidable because two-counter machines simulate Turing machines. Given such a machine $\mathcal{M}$, one builds a two-clock game $\mathcal{G}_{\mathcal{M}}$ with non-negative weights in which Min simulates $\mathcal{M}$, with counter values encoded in clock values and modules that test the encoding. If $\mathcal{M}$ does not halt, the value from $(q_i, \mathbf{0})$ is at most $64$; if $\mathcal{M}$ halts in at most $N$ steps, the value is at least $64 + \frac{11}{12 \cdot 30^{5N}}$. So the value is at most $64$ exactly when $\mathcal{M}$ does not halt.

## Sources

- Quentin Guilmant, Joël Ouaknine and Isa Vialard, "The Value Problem for Weighted Timed Games with Two Clocks is Undecidable", in *Foundations of Software Science and Computation Structures (FoSSaCS 2026)*, Lecture Notes in Computer Science, Springer, 2026, pp. 616–635, doi:10.1007/978-3-032-22730-0_29; read as arXiv:2507.10550v2, <https://arxiv.org/abs/2507.10550v2>, which carries the title and authors of the conference paper: Theorem 1 (the undecidability theorem, stated in the introduction and proved in the section on two-clock games) with the reduction proposition and the definitions of weighted timed games and the value problem, in the numbering of that version. The later arXiv version, Quentin Guilmant, Joël Ouaknine, Isa Vialard and Angel Wuttke, "(Un)Decidability of Two-Clock Weighted Timed Games", arXiv:2507.10550v3, <https://arxiv.org/abs/2507.10550v3>, extends it: Theorem 3.1, Proposition 3.2 (the value gap) and the decidability result for almost divergent games, in the numbering of that version.
