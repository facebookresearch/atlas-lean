# Weighted radius at least $K$ for trees as a decision problem

The decision problem WEIGHTED DIAMETER with radius $K$ or greater for trees accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding (natural numbers in binary), to an instance $(n, E, C, K)$ that is well formed (a simple edge list on $\{0, \dots, n-1\}$ forming a tree, $|C| = |E|$, $K > 0$) and feasible (some rearrangement of $C$ as edge lengths gives radius at least $K$). It rejects every bitstring that does not decode to an instance.
