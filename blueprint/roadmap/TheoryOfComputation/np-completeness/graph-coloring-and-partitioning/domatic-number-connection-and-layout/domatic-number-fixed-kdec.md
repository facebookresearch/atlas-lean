# DOMATIC NUMBER FOR FIXED K as a decision problem

Fix a natural number $K$. The decision problem DOMATIC NUMBER FOR FIXED K accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs $(n, E)$ of a vertex count and an edge list, to an instance that is well-formed and [feasible](domatic-number-feasible.md) for DOMATIC NUMBER with bound $K$. It rejects every bitstring that does not decode to such an instance.
