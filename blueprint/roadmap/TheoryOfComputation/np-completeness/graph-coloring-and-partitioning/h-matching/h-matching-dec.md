# H-MATCHING as a decision problem

For a pattern graph $H$ on $\{0, \dots, m-1\}$ with edge list $hs$, the decision problem
H-MATCHING accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding of its instances, to an instance that is [well-formed](../acyclic-coloring/well-formed.md) and [feasible
for $H$](hmatching-feasible.md). It rejects every bitstring that does not decode to an instance.
