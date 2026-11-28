# DOMATIC NUMBER as a decision problem

The decision problem DOMATIC NUMBER accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$ of a vertex count, an edge list and a bound, to an instance that is [well-formed](well-formed-3.md) and [feasible](domatic-number-feasible.md) for DOMATIC NUMBER. It rejects every bitstring that does not decode to such an instance.
