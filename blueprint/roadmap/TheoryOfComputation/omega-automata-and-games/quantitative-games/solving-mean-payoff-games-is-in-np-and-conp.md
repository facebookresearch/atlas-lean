# Solving mean-payoff games is in NP ∩ coNP

Given a finite [mean-payoff game](classical-quantitative-objectives.md) with integer weights in binary, a vertex $v$ and a rational threshold $x$,
deciding whether $\mathrm{val}(v) \ge x$ is in [NP](../../complexity-classes/the-classes-p-np-and-conp/np.md) $\cap$
[coNP](../../complexity-classes/the-classes-p-np-and-conp/co-np.md). A certificate for either answer is a positional optimal strategy of the
corresponding player, checked in polynomial time by solving the minimum (or maximum) cycle mean problem on the cyclic components
of the one-player game it leaves that are reachable from $v$. No polynomial-time algorithm is known; see
[polynomial-time solvability of mean-payoff games](../polynomial-time-solvability-of-mean-payoff-games.md).

## Depends on

- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)
- [The class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The class coNP](../../complexity-classes/the-classes-p-np-and-conp/co-np.md)

## Proof depends on

- [Karp's minimum cycle mean theorem](../../../ComputerScience/graph-algorithms/shortest-paths/minimum-cycle-mean/karp-min-cycle-mean.md)
- [Energy, mean-payoff and total-payoff games are positionally determined](positional-determinacy-of-mean-payoff-and-energy-games.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): Section 5.2, Theorem 5.2 with its proof, and the bibliographic references crediting the NP and coNP bound to A. Puri (1995).
