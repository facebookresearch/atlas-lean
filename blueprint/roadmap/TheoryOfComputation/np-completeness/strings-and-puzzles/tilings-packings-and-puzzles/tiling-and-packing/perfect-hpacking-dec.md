# PERFECT H-PACKING as a decision problem

Fix a pattern graph $H = (m, hs)$. The decision problem PERFECT H-PACKING accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs $(n, E)$ of a vertex count and an edge list, to an instance that is well-formed and feasible for PARTITION INTO ISOMORPHIC SUBGRAPHS with pattern $H$. It rejects every bitstring that does not decode to such an instance.
