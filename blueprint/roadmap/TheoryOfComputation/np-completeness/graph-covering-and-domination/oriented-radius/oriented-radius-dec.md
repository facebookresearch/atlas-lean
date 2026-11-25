# ORIENTED RADIUS as a decision problem

The decision problem ORIENTED RADIUS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$, to an instance that is well-formed for ORIENTED DIAMETER and some orientation of whose graph has radius at most $K$. It rejects every bitstring that does not decode to such an instance.
