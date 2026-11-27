# MINIMUM t-SPANNER as a decision problem

Fix a natural number $t$. The decision problem MINIMUM t-SPANNER accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$, to an instance that is well-formed for MINIMUM t-SPANNER and whose graph has a $t$-spanner with at most $K$ edges. It rejects every bitstring that does not decode to such an instance.
