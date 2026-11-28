# Core verification in stochastic lossy channel games is undecidable

For concurrent stochastic games over a lossy channel whose players have almost-sure LTL objectives, no algorithm decides whether some, or every, strategy profile in the core satisfies a given almost-sure LTL property.

**Lossy channel arenas.** A channel holds a word $\mu \in M^*$ over a finite message alphabet $M$; after each round every message is lost independently with a fixed rational probability $\lambda \in (0, 1)$. A *channel operation* is $\mathit{nop}$, $!m$ (append $m$ at the front, $\mu \mapsto m\mu$) or $?m$ (remove $m$ from the end, $wm \mapsto w$, undefined if $\mu$ does not end with $m$). An $n$-player *concurrent stochastic lossy channel arena* $(\{1, \dots, n\}, L, M, \{\mathit{Act}_i\}, \mathit{Tab}, l_0)$ has a set $L$ of locations with initial location $l_0$, pairwise disjoint finite action sets $\mathit{Act}_i$, and a map $\mathit{Tab}$ that assigns to a location and an action profile a probability distribution, with rational probabilities, over pairs of a next location and a channel operation. States are words $l\mu$ with $l \in L$ and $\mu \in M^*$, starting from $l_0$ with the empty channel. In each round all players choose actions at once, among those that cannot lead to an undefined channel operation; a next location and operation are drawn from $\mathit{Tab}$, the operation is applied and messages are lost. Strategies map histories of states to distributions over allowed actions, and a strategy profile induces a probability measure on infinite paths.

**Objectives and the core.** For an LTL formula $\varphi$, the *almost-sure* property $\mathsf{AS}(\varphi)$ holds for a profile when the paths satisfying $\varphi$ have probability $1$. A *game* adds an objective $\Phi_i$ for each player $i$; player $i$ *wins* under a profile if $\Phi_i$ holds. A joint strategy of a nonempty coalition $C$ is a *beneficial deviation* from a profile $\vec\sigma$ if all members of $C$ lose under $\vec\sigma$ and all win whatever the other players do. The *core* is the set of profiles that admit no beneficial deviation. Given a game and a property $\Gamma$, *E-Core* asks whether some profile in the core satisfies $\Gamma$, and *A-Core* asks whether every profile in the core does.

**Proposition (Stan, Najib, Lin and Abdulla).** When the objectives of the players and the property $\Gamma$ are almost-sure LTL properties, E-Core and A-Core are undecidable (Proposition 17 of the source).

The same paper shows that both problems become decidable when the objectives are almost-sure reachability or safety and $\Gamma$ is an almost-sure conjunction of reachability, safety or Büchi conditions.

## Depends on

- [Formulas of linear temporal logic](../../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Take a game with a single player whose objective is $\Phi = \mathsf{AS}(\mathbf{G}\mathbf{F} R_1 \wedge \mathbf{F}\mathbf{G} R_2)$ and set $\Gamma = \Phi$. A profile in the core satisfies $\Gamma$ exactly when the player has a strategy achieving $\Phi$ on the lossy channel system, a one-player stochastic game over a lossy channel; deciding this is undecidable by a result of Baier, Bertrand and Schnoebelen on probabilistic lossy channel systems, as the source recalls. A good expansion links a page for that result.

## Sources

- D. Stan, M. Najib, A. W. Lin and P. A. Abdulla, "Concurrent Stochastic Lossy Channel Games", in *32nd EACSL Annual Conference on Computer Science Logic (CSL 2024)*, Leibniz International Proceedings in Informatics (LIPIcs) 288, 2024, paper 46, doi:10.4230/LIPIcs.CSL.2024.46; read as arXiv:2311.17037v1, <https://arxiv.org/abs/2311.17037v1>: Proposition 17 in Section 4 (undecidability of E-Core and A-Core for almost-sure LTL objectives) with the argument before it, the definitions of channel operations, arenas, strategies, objectives, beneficial deviations and the core in Sections 3 and 4, and Theorem 32 (the decidability theorem of Section 7), in the numbering of that version.
