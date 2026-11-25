# GRAPH PARTITIONING WITH UNIT WEIGHTS as a decision problem

Fix a natural number $K$. The decision problem GRAPH PARTITIONING WITH UNIT WEIGHTS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of quadruples $(n, w, E, J)$, to an instance that is well-formed for block bound $K$ and for which the GRAPH PARTITIONING instance $(n, w, E, K, J)$ is feasible: the vertices can be split into blocks each containing at most $K$ vertices so that at most $J$ edges join different blocks. It rejects every bitstring that does not decode to such an instance.
