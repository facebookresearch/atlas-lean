# Parity, mean-payoff, discounted and simple stochastic games, and the ARRIVAL switch-graph problem, lie in UEOPL

Solving a parity game, a mean-payoff game, a discounted game and a simple stochastic game are each in UEOPL. ARRIVAL takes a switch graph: each vertex $v$ has two successors $s_0(v),s_1(v)$; a train starts at $o$, and at every visit of $v$ leaves along the current switch of $v$, after which the switch flips. The decision problem asks whether the train reaches $d$; the search problem asks for the unique efficiently verifiable witness of the run (switch-usage counts). The decision version is in $\mathsf{UP}\cap\mathsf{coUP}$, the search version lies in CLS and in fact in UEOPL, and both are solvable in randomized time $O(1.4143^n)$ on $n$-vertex switch graphs.

## Proof sketch

Simple stochastic games reduce both to contraction and to P-LCP, giving two proofs of UEOPL membership; discounted, mean-payoff and parity games reduce to simple stochastic games. For ARRIVAL, termination has an efficiently verifiable unique witness (a switching flow recording how often each edge is traversed), and finding it can be cast as following a line with a potential; the END-OF-POTENTIAL-LINE instance always contains exactly one line, so the problem is in UEOPL. Efficient sampling of the state space gives the randomized algorithm.

## Depends on

- [Parity game](../../../omega-automata-and-games/parity-games/parity-game.md)
- [UNIQUE-EOPL, the class UEOPL and PromiseUEOPL: one potential line certified by violation solutions](unique-eopl-and-ueopl.md)

## Proof depends on

- [Piecewise-linear contraction fixpoints in any ℓp norm lie in UEOPL and are polynomial-time in fixed dimension](pl-contraction-in-ueopl.md)
- [The P-matrix linear complementarity problem lies in UEOPL, giving an expected 2^(n/2) poly(n)-time algorithm](p-matrix-lcp-in-ueopl.md)

## Sources

- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", ICALP (2019), arXiv:1811.03841.
- Bernd Gärtner, Thomas Dueholm Hansen, Pavel Hubáček, Karel Král, Hagar Mosaad and Veronika Slívová, "ARRIVAL: Next Stop in CLS", ICALP (2018), arXiv:1802.07702.
