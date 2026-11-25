# s-CLUB as a decision problem

Fix a natural number $s$. The decision problem s-CLUB accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$, to an instance that is well-formed for s-CLUB and whose graph has a set of at least $K$ vertices inducing a subgraph of diameter at most $s$. It rejects every bitstring that does not decode to such an instance.
