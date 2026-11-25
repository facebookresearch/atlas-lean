# GRAPH k-COLORABILITY as a decision problem

Fix a natural number $k$. The decision problem GRAPH $k$-COLORABILITY accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$ (a natural number, a list of pairs of natural numbers and a natural number), to an instance that is well-formed for GRAPH $k$-COLORABILITY and whose graph is $K$-colorable: its vertices can be colored with $0, \dots, K-1$ so that adjacent vertices receive different colors. It rejects every bitstring that does not decode to such an instance.
