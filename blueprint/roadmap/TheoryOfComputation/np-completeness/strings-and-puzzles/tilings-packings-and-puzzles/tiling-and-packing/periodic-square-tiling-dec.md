# PERIODIC SQUARE-TILING WITH BOUNDED PERIOD as a decision problem

The decision problem PERIODIC SQUARE-TILING WITH BOUNDED PERIOD accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(C, T, N)$ of a color list, a tile list and a side length, to an instance that is well-formed for SQUARE TILING ($C$ lists distinct colors, $T$ lists distinct tiles, every tile color is in $C$, and $0 < N \le |C|$) and feasible for PERIODIC SQUARE-TILING WITH BOUNDED PERIOD. It rejects every bitstring that does not decode to such an instance.
