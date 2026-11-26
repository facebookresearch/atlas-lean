# The frontier lower bound for nondeterministic circuits

The unconditional frontier lower bound holds for nondeterministic circuits with any number of witness inputs: if $S_n$ is as in the unconditional frontier theorem, every nondeterministic circuit of fan-in at most $r$ deciding $S_n$ (i.e. $x\in S_n$ iff some witness $y$ makes the output accept) has $s$ multiary gates with $(r-1)s>(2-\varepsilon)n$ for large $n$.

## Proof sketch

Hiding the witness inputs of the compiled constraint network (existentially quantifying them in each local constraint) gives a network on the same graph accepting exactly $S_n$ that reads only the ordinary inputs; the cycle-rank accounting and the sweep argument are unchanged.

## Depends on

- [Nondeterministic and conondeterministic circuits](../simulations-between-circuit-bases/nondeterministic-and-conondeterministic-circuits.md)
- [Rectangle-free sets and rectangle bias](rectangle-free-sets-and-rectangle-bias.md)

## Proof depends on

- [Unconditional frontier lower bounds of (2 - ε)n](unconditional-frontier-lower-bounds.md)
- [From small circuits to wide constraint networks](from-circuits-to-constraint-networks.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
