# Energy, mean-payoff and total-payoff games are positionally determined

Over finite arenas the [objectives](classical-quantitative-objectives.md) reachability, energy, $\mathrm{MeanPayoff}^-$, $\mathrm{MeanPayoff}^+$
and total payoff are uniformly bi-positional: in every finite game with one of these objectives both players have positional
strategies that are optimal from every vertex, and the game is determined. For mean-payoff games this is the theorem of
Ehrenfeucht and Mycielski. The proof first shows that a single player who controls every vertex has a positional optimal
strategy (for mean payoff: follow a path to a reachable simple cycle of best average and repeat it), and then lifts
positionality from one-player to two-player finite arenas.

Shortest-path games are only half-positional over finite arenas: Max has a positional optimal strategy, but Min may have no
optimal strategy at all (a Min vertex with a self-loop of weight $-1$ and an edge to $\mathrm{Win}$ has value $-\infty$, and both positional strategies
of Min are worse) or may need memory to play optimally (counting passes through a cycle before leaving it). The cited Theorem 4.4
lists shortest path among the bi-positional objectives, which Section 5.4 of the same book contradicts.

## Depends on

- [Reachability and safety games are positionally determined and solvable in linear time](../muller-rabin-and-streett-games/reachability-and-safety-games.md)
- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 4 (A. Casares, P. Ohlmann and P. Vandenhove, "Positionality and memory"): Theorem 4.4 with its partial proof for $\mathrm{MeanPayoff}^-$, using Theorem 4.3 (the one-to-two-player lift over finite arenas).
- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): the bibliographic references at the end of the chapter, crediting positional determinacy of mean-payoff games to A. Ehrenfeucht and J. Mycielski, *International Journal of Game Theory* 8 (1979).
- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): Section 5.4, Figures 5.3 and 5.4 and Theorem 5.12 (positional determinacy for Max in shortest-path games, called there a half-positional determinacy result).
