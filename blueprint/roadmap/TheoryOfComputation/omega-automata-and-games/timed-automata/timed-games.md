# Timed games

A *timed arena* is a tuple $(L, C, E_{\mathrm{Eve}}, E_{\mathrm{Adam}}, c)$ of a finite set $L$ of locations, a finite set $C$ of clocks, sets $E_{\mathrm{Eve}}, E_{\mathrm{Adam}} \subseteq L \times \Phi_C \times 2^C \times L$
of edges controlled by Eve and by Adam, each with a guard (a clock constraint, conjunctive and with integer bounds as for [zones](zones-and-difference-bound-matrices.md)) and a set of clocks to reset, and a colouring $c$ of the edges, as in
[timed automata](timed-buchi-automata.md). Configurations are pairs $(\ell, \nu)$ with $\nu \in \mathbb{R}_{\ge 0}^C$. In a configuration both players propose an action $(d, e)$: a delay $d \ge 0$
and one of their edges $e = (\ell, g, R, \ell')$ with $\nu + d \models g$ (or a dummy action, available only when the player has no edge action); if both propose edge actions the one with the smaller delay is
performed, ties going to Adam, and if only one does it is performed whatever its delay (arenas in which neither player has an edge action in some reachable configuration are excluded here), leading to $(\ell', (\nu + d)[R \leftarrow 0])$. A *timed game* adds a winning condition on the sequence of colours, and the
*timed reachability game* problem asks whether Eve has a (deterministic) strategy that reaches a target set from $(\ell_0, \vec 0)$.

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)
- [Zones and difference-bound matrices](zones-and-difference-bound-matrices.md)
- [Arenas, strategies and memory structures](../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 11 (N. Markey and O. Sankur, "Timed games"): Section 11.1, Definition 11.1, the semantics of actions and steps that follows it, and Problem 11.1 (solving a timed reachability game).
