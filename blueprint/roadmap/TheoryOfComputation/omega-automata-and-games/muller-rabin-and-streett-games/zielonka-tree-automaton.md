# The Zielonka tree automaton of a Muller condition

Let $C = \{1, \dots, d\}$ and let $\mathrm{Muller}(\mathcal{F})$ be a [Muller objective](muller-rabin-and-streett-objectives.md) with
[Zielonka tree](zielonka-tree-of-a-muller-condition.md) $T_{\mathcal{F}}$. There is a deterministic parity automaton over $C$
accepting exactly $\mathrm{Muller}(\mathcal{F})$ whose states are the branches of $T_{\mathcal{F}}$ and whose parity condition uses as many
priorities as the height of $T_{\mathcal{F}}$, hence at most $d$.

## Depends on

- [Zielonka tree of a Muller condition](zielonka-tree-of-a-muller-condition.md)
- [Nondeterministic parity automaton](../parity-automata/parity.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 3 (N. Fijalkow and F. Horn, "Regular games"): Theorem 3.6 and its proof.
