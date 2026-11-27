# Solving mean-payoff games and parity games is in UP ∩ coUP

Deciding, for a finite [mean-payoff game](classical-quantitative-objectives.md) with integer weights in binary, a vertex $v$ and a binary-encoded rational $x$, whether
$\mathrm{val}(v) \ge x$, and deciding whether Eve wins a finite [parity game](../parity-games/parity-game.md) from a given vertex, are in
$\mathrm{UP} \cap \mathrm{coUP}$ ($\mathrm{UP}$: problems decided by a nondeterministic polynomial-time machine with at most one accepting computation;
$\mathrm{coUP}$: their complements). The bound follows by reducing parity games to mean-payoff games, mean-payoff games to
discounted-payoff games, and placing the latter in $\mathrm{UP} \cap \mathrm{coUP}$.

## Depends on

- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)
- [Parity game](../parity-games/parity-game.md)

## Proof depends on

- [Mean-payoff values are rationals with small denominators](mean-payoff-values-are-rationals-with-small-denominators.md)
- [Discounted payoff approximates mean payoff](discounted-payoff-approximates-mean-payoff.md)
- [Solving discounted-payoff games is in UP ∩ coUP](solving-discounted-payoff-games-is-in-up-and-coup.md)
- [Parity games reduce to mean-payoff games](parity-games-reduce-to-mean-payoff-games.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): Section 5.3, Corollary 5.4 with its proof.
