# The value problem for two-clock weighted timed games is undecidable

No algorithm decides, given a weighted timed game with two clocks, a starting location and a rational threshold $c$, whether the value of the game is at most $c$; this holds already with non-negative weights.

The games are those of Definitions 1 and 2 of the source, which differ from the [weighted timed games](weighted-timed-games.md) of Busatto-Gaston, Monmege and Reynier as follows. Clock constraints are $x \sim n$ or $x - y \sim n$ (diagonal constraints allowed) with $n \in \mathbb{N}$ and ${\sim} \in \{<, \le, =, \ge, >\}$, and clocks are not bounded. A game $\mathcal{G} = (L_{\mathrm{Min}}, L_{\mathrm{Max}}, G, \mathcal{X}, T, w)$ has goal locations $G \subseteq L_{\mathrm{Min}}$, transitions $T \subseteq (L \setminus G) \times 2^{\mathcal{C}} \times 2^{\mathcal{X}} \times L$ (a set of clock constraints to satisfy and a set of clocks to reset) and integer weights $w$ on the non-goal locations and on the transitions, and no final weights; no configuration outside $G$ is deadlocked. A delay $d$ followed by a transition $t$ from location $\ell$ has weight $d \cdot w(\ell) + w(t)$; a play (maximal run) has the accumulated weight of its moves if it reaches a goal location and weight $+\infty$ otherwise. Strategies map finite non-maximal runs ending in a player's location to a delay and a transition, and turn-based games are determined, with value $\mathsf{Val}_{\mathcal{G}}(\ell, \nu)$. A game is *turn-based* when each location belongs to one player, and *time-bounded* when every play lasts at most a fixed amount of time.

**Theorem (Guilmant, Ouaknine and Vialard).** The *value problem* (Definition 2), which asks, given such a game, a starting location $\ell_0$ and a rational threshold $c$, whether $\mathsf{Val}_{\mathcal{G}}(\ell_0, \mathbf{0}) \le c$, is undecidable for two-player, turn-based, time-bounded weighted timed games with two clocks and non-negative integer weights (Theorem 1 of arXiv:2507.10550v2). The same holds for games over unbounded time that satisfy the other hypotheses.

The value problem is decidable for one-clock weighted timed games, and it was known to be undecidable from three clocks on (Bouyer, Jaziri and Markey), as the source recalls. The extended version of the paper also shows that the value of almost divergent turn-based two-clock weighted timed games is computable in triply exponential time.

## Depends on

- [Weighted timed games](weighted-timed-games.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from the halting problem for deterministic two-counter machines, undecidable because two-counter machines simulate Turing machines. Given such a machine $\mathcal{M}$, one builds a two-clock game $\mathcal{G}_{\mathcal{M}}$ with non-negative weights in which Min simulates $\mathcal{M}$, with counter values encoded in clock values and modules that test the encoding. If $\mathcal{M}$ does not halt, the value from $(q_i, \mathbf{0})$ is at most $64$; if $\mathcal{M}$ halts in at most $N$ steps, the value is at least $64 + \frac{11}{12 \cdot 30^{5N}}$. So the value is at most $64$ exactly when $\mathcal{M}$ does not halt.

## Sources

- Quentin Guilmant, Joël Ouaknine and Isa Vialard, "The Value Problem for Weighted Timed Games with Two Clocks is Undecidable", in *Foundations of Software Science and Computation Structures (FoSSaCS 2026)*, Lecture Notes in Computer Science, Springer, 2026, pp. 616–635, doi:10.1007/978-3-032-22730-0_29; read as arXiv:2507.10550v2, <https://arxiv.org/abs/2507.10550v2>, which carries the title and authors of the conference paper: Theorem 1 (the undecidability theorem, stated in the introduction and proved in the section on two-clock games) with Proposition 1 (the reduction) and Definitions 1 and 2 (weighted timed games and the value problem), in the numbering of that version. The later arXiv version, Quentin Guilmant, Joël Ouaknine, Isa Vialard and Angel Wuttke, "(Un)Decidability of Two-Clock Weighted Timed Games", arXiv:2507.10550v3, <https://arxiv.org/abs/2507.10550v3>, extends it: Theorem 3, Proposition 4 (the value gap) and Theorem 20 (decidability for almost divergent games, with the complexity analysis after it), in the numbering of that version.
