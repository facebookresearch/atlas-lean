# Weighted timed games

A weighted timed game is a timed automaton whose locations are split between two players and whose locations and edges carry integer weights, with weights on locations paid per time unit; player Min tries to reach a target while minimizing the accumulated weight plus a final weight, and player Max tries to prevent it or to maximize that weight.

**Definition.** Let $\mathcal{X}$ be a finite nonempty set of clocks, valued in $\mathbb{R}_{\ge 0}$, and let guards be finite conjunctions of constraints $x \bowtie c$ with $x \in \mathcal{X}$, $c \in \mathbb{Z}$ and ${\bowtie} \in \{<, \le, \ge, >\}$, as for [timed automata](../timed-buchi-automata.md). A *weighted timed game* (WTG) is a tuple $\mathcal{G} = \langle L_{\mathrm{Min}}, L_{\mathrm{Max}}, \mathcal{X}, L_T, E, \mathrm{wt}, \mathrm{wt}_T \rangle$ where $L = L_{\mathrm{Min}} \uplus L_{\mathrm{Max}}$ is a finite set of locations split between the players, $E \subseteq L \times \mathrm{Guards}(\mathcal{X}) \times 2^{\mathcal{X}} \times L$ is a finite set of edges $\ell \xrightarrow{g, Y} \ell'$ with a guard and a set of clocks to reset, $\mathrm{wt} : E \uplus L \to \mathbb{Z}$ gives integer weights to edges and locations, $L_T \subseteq L_{\mathrm{Min}}$ is a set of target locations, and $\mathrm{wt}_T$ assigns a final weight in $\mathbb{R} \cup \{\pm\infty\}$ to each target configuration.

The configurations are the pairs $(\ell, \nu)$ of a location and a clock valuation, belonging to the owner of $\ell$. From $(\ell, \nu)$, for a delay $d \ge 0$ and an edge $e = \ell \xrightarrow{g, Y} \ell'$ with $\nu + d \models g$, there is a move to $(\ell', (\nu + d)[Y := 0])$ of weight $d \cdot \mathrm{wt}(\ell) + \mathrm{wt}(e)$. The standing hypotheses are that the transition system is free of deadlocks outside $L_T$ and no edges leave $L_T$, that guards are non-diagonal with integer constants, that clocks are bounded by the largest constant $M$ of the guards (configurations are restricted to $L \times [0, M]^{\mathcal{X}}$), and that final weights are piecewise affine functions, continuous on regions. Plays are maximal paths; a strategy of a player maps each finite play ending in one of his configurations to a delay and an edge enabled there. The weight of a play is $+\infty$ if it never reaches $L_T$, and otherwise the sum of the weights of its moves plus the final weight of the target configuration it ends in. The *value* of a strategy of Min is the supremum of the weights of the plays it allows, the value of a strategy of Max is the infimum, and the lower and upper values of a configuration are $\sup$ over Max strategies and $\inf$ over Min strategies of these. Turn-based weighted timed games are determined, so both coincide; this common value is written $\mathrm{Val}_{\mathcal{G}}(\ell, \nu) \in \mathbb{R} \cup \{\pm\infty\}$.

The value is $-\infty$ when Min can force plays of arbitrarily negative weight, for instance by repeatedly closing a cycle of negative weight before reaching a target. Without final weights (all equal to $0$) the model is the priced timed game of the earlier literature.

## Depends on

- [Timed games](../timed-games.md)
- [Timed Büchi automata and timed regular languages](../timed-buchi-automata.md)

## Proof depends on

None.

## Sources

- D. Busatto-Gaston, B. Monmege and P.-A. Reynier, "Optimal controller synthesis for timed systems", *Logical Methods in Computer Science* 19(1):20, 2023, doi:10.46298/lmcs-19(1:20)2023, <https://lmcs.episciences.org/7419>; numbering of arXiv:2104.12577v5: Section 2.1 (clocks, valuations and guards), the definition of weighted timed games and their semantics, strategies and values in Section 2.4, Hypotheses 1 to 4, and the determinacy remark after them.
