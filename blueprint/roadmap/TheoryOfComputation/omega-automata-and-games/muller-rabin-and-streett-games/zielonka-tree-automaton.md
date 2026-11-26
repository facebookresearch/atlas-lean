# The Zielonka tree automaton of a Muller condition

Let $C = \{1, \dots, d\}$ and let $\mathrm{Muller}(\mathcal{F})$ be a [Muller objective](muller-rabin-and-streett-objectives.md) with
[Zielonka tree](zielonka-tree-of-a-muller-condition.md) $T_{\mathcal{F}}$. There is a deterministic parity automaton over $C$
with acceptance on transitions (each transition, rather than each state, carries a priority, and a run is accepting when the largest
priority occurring infinitely often on its transitions is even) accepting exactly $\mathrm{Muller}(\mathcal{F})$, whose states are the branches of
$T_{\mathcal{F}}$ and whose parity condition uses as many priorities as the height of $T_{\mathcal{F}}$, the number of nodes on a longest branch, hence at
most $d$.

## Depends on

- [Muller, Rabin and Streett objectives](muller-rabin-and-streett-objectives.md)
- [Zielonka tree of a Muller condition](zielonka-tree-of-a-muller-condition.md)
- [Nondeterministic parity automaton](../parity-automata/parity.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 3 (N. Fijalkow and F. Horn, "Regular games"): Theorem 3.6 and its proof.
