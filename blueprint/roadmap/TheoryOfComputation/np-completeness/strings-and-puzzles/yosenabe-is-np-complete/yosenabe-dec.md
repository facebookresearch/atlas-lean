# YOSENABE as a decision problem

The decision problem YOSENABE accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a well-formed Yosenabe puzzle (a nonempty rectangular grid of cell contents $(k, a)$ with $k \le 2$, positive circle numbers, and at most one label per gray area) that is feasible (arrows from all circles into gray areas satisfying the rules). It rejects every bitstring that does not decode to an instance.
