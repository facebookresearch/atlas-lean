# UPPER DOMINATION as a decision problem

The decision problem UPPER DOMINATION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$ (a natural number, a list of pairs of natural numbers and a natural number), to an instance that is well-formed for UPPER DOMINATION and feasible for it (some minimal dominating set has at least $K$ vertices). It rejects every bitstring that does not decode to such an instance.
