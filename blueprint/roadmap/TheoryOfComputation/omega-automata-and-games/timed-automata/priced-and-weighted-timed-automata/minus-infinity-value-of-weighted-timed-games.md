# The minus-infinity value problem for weighted timed games is undecidable

No algorithm decides, given a weighted timed game and an initial location, whether the value of the game from that location with all clocks at zero is $-\infty$.

**Theorem.** It is undecidable, given a [weighted timed game](weighted-timed-games.md) $\mathcal{G}$ and an initial location $\ell_I$, whether $\mathrm{Val}_{\mathcal{G}}(\ell_I, \mathbf{0}) = -\infty$, where $\mathbf{0}$ is the valuation with all clocks equal to $0$ (Proposition 3.12 of the source). This holds already when every final weight is $0$: the proof adds to a game without final weights an edge of weight $-\alpha$ from its target back to the initial location and a new target of final weight $0$, reducing the undecidable problem whether Min can guarantee reaching the target with weight $< \alpha$.

The problem becomes decidable, and $\mathbf{EXP}$-complete, for almost-divergent weighted timed games, in which every play following a cycle of the region abstraction has weight at most $-1$, exactly $0$ or at least $1$, with a further condition on cycles of weight $0$ (Proposition 3.11 of the source); this decidable case is what lets the source compute the configurations of value $-\infty$ before approximating the other values.

## Depends on

- [Weighted timed games](weighted-timed-games.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the existence problem for weighted timed games without final weights: given $\mathcal{G}$, a target location $\ell_T$, an initial location $\ell_I$ and a non-negative integer threshold $\alpha$, does Min have a strategy guaranteeing to reach $\ell_T$ from $\ell_I$ with weight $< \alpha$? This problem is undecidable (Bouyer, Brihaye and Markey for non-negative weights and the comparison $\le \alpha$; Brihaye, Geeraerts, Narayanan Krishna, Manasa, Monmege and Trivedi for arbitrary weights and all comparisons). From $\mathcal{G}$ build $\mathcal{G}'$ by adding an edge from $\ell_T$ back to $\ell_I$ with no guard, resetting all clocks and of weight $-\alpha$, a new target $\ell'_T$ reached from $\ell_T$ by an edge of weight $0$, and giving $\ell_T$ and $\ell'_T$ to Min. If Min can guarantee weight $< \alpha$ in $\mathcal{G}$, she can repeat a play of weight $< \alpha$ followed by the edge of weight $-\alpha$, a cycle of negative weight, as often as she likes, so $\mathrm{Val}_{\mathcal{G}'}(\ell_I, \mathbf{0}) = -\infty$; conversely, value $-\infty$ in $\mathcal{G}'$ forces either value $-\infty$ in $\mathcal{G}$ or plays from $(\ell_I, \mathbf{0})$ to $\ell_T$ of weight below $\alpha$.

## Sources

- D. Busatto-Gaston, B. Monmege and P.-A. Reynier, "Optimal controller synthesis for timed systems", *Logical Methods in Computer Science* 19(1):20, 2023, doi:10.46298/lmcs-19(1:20)2023, <https://lmcs.episciences.org/7419>; numbering of arXiv:2104.12577v5: Proposition 3.12 with its proof, Proposition 3.11 (the almost-divergent case) and the definition of almost-divergent games, in Section 3.
