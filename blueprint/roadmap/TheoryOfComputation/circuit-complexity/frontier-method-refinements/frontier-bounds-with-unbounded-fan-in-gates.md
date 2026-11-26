# Frontier lower bounds with a few gates of unbounded fan-in

Call a gate of arity $k$ *aggregating* in a commutative monoid $T$ if its value is read off from a product in $T$ of contributions of its individual arguments (for example threshold gates with arbitrary weights, aggregating in $(\mathbb{R},+)$ restricted to finitely many attainable values, or parity, AND and OR gates). If a circuit of fan-in at most $r$ additionally contains special aggregating gates whose partial products can be stored in a *ledger* with few possible values per sweep step, then the frontier lower bound still applies with the ledger size added to the message count; in particular circuits with an unbounded-weight threshold gate on top of fan-in-two subcircuits deciding rectangle-free sets need nearly $(2-\varepsilon)n$ multiary gates.

## Proof sketch

Erase the special gates from the network and carry their running partial products as an extra component of each sweep message; the counting lemma tolerates a multiplicative increase in the number of messages, which is subexponential when the ledger takes few values.

## Depends on

- [Layouts of multigraphs, cycle rank and the layout hypothesis](../frontier-method/layouts-and-the-layout-hypothesis.md)
- [Threshold gates and the basis of threshold circuits](../parallel-circuit-hierarchies/threshold-gates-and-threshold-circuits.md)

## Proof depends on

- [Unconditional frontier lower bounds of (2 - ε)n](../frontier-method/unconditional-frontier-lower-bounds.md)
- [Sweeps and the frontier counting lemma](../frontier-method/sweeps-and-the-frontier-counting-lemma.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
