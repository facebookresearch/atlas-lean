# From small circuits to wide constraint networks

A *constraint network* over an alphabet $U$ is a multigraph whose edges carry values in $U$ and whose vertices impose local constraints on the values of their incident edges; some edges are labelled by input coordinates. Every circuit of fan-in at most $r$ with $s$ multiary gates (arity at least two) deciding $S\subseteq U^n$ compiles into a constraint network of maximum degree at most $r+1$ that accepts exactly $S$ (each accepted input has a unique satisfying edge assignment), in which the cycle rank plus the number of inputs read is at most $(r-1)s+1$. Sweeping the network along any layout yields a sweep of $S$ whose messages are the values on the cut edges, so a layout of width $w$ gives at most $|U|^{w}$ messages per step.

## Proof sketch

Each gate becomes a vertex constraining its output wire and argument wires; fan-out is realized by copy vertices; constant and unary gates are merged away and contribute nothing to the cycle rank. Counting edges and vertices gives the cycle-rank bound.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)
- [Layouts of multigraphs, cycle rank and the layout hypothesis](layouts-and-the-layout-hypothesis.md)
- [Sweeps and the frontier counting lemma](sweeps-and-the-frontier-counting-lemma.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
