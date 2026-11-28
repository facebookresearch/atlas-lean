# BUILDING PUZZLE as a decision problem

The decision problem BUILDING PUZZLE accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a partial Latin square instance and four lists, to an instance that is [well-formed](well-formed-2.md) and [feasible](building-puzzle-feasible.md) for BUILDING PUZZLE. It rejects every bitstring that does not decode to such an instance.
