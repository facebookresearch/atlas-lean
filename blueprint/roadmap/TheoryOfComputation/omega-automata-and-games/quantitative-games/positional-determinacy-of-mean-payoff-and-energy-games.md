# Shortest-path, energy, mean-payoff and total-payoff games are positionally determined

Over finite arenas the [objectives](classical-quantitative-objectives.md) reachability, shortest path, energy, $\mathrm{MeanPayoff}^-$, $\mathrm{MeanPayoff}^+$
and total payoff are uniformly bi-positional: in every finite game with one of these objectives both players have positional
strategies that are optimal from every vertex, and the game is determined. For mean-payoff games this is the theorem of
Ehrenfeucht and Mycielski. The proof first shows that a single player who controls every vertex has a positional optimal
strategy (for mean payoff: follow a path to a reachable simple cycle of best average and repeat it), and then lifts
positionality from one-player to two-player finite arenas.

## Depends on

- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 4 (A. Casares, P. Ohlmann and P. Vandenhove, "Positionality and memory"): Theorem 4.4 with its partial proof for $\mathrm{MeanPayoff}^-$, using Theorem 4.3 (the one-to-two-player lift over finite arenas).
- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): the bibliographic references at the end of the chapter, crediting positional determinacy of mean-payoff games to A. Ehrenfeucht and J. Mycielski, *International Journal of Game Theory* 8 (1979).
