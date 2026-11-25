# GRAPH COLORING ON DUALLY CHORDAL GRAPHS as a decision problem

The decision problem GRAPH COLORING ON DUALLY CHORDAL GRAPHS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$ (a natural number, a list of pairs of natural numbers and a natural number), to an instance that is well-formed for GRAPH COLORING ON DUALLY CHORDAL GRAPHS and whose graph is $K$-colorable: its vertices can be colored with $0, \dots, K-1$ so that adjacent vertices receive different colors. It rejects every bitstring that does not decode to such an instance.
