# PACKING WITH DISCS as a decision problem

The decision problem PACKING WITH DISCS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(d, P, K)$ of a size, a list of polygon cells and a bound, to an instance that is well-formed for PACKING SQUARES IN A RECTILINEAR POLYGON ($d > 0$, the cells are distinct and form a polyomino, and $K > 0$) and feasible for PACKING WITH DISCS. It rejects every bitstring that does not decode to such an instance.
