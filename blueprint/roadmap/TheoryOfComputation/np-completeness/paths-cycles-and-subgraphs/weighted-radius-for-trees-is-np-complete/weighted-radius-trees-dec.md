# WEIGHTED RADIUS for trees as a decision problem

The decision problem WEIGHTED RADIUS for trees accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding (natural numbers in binary), to an instance $(n, E, C, K)$ that is well formed (a simple edge list on $\{0, \dots, n-1\}$ whose graph is a tree, $|C| = |E|$, $K > 0$) and feasible (some rearrangement of $C$ as edge lengths gives a centre within distance $K$ of every vertex). It rejects every bitstring that does not decode to an instance.
