# DISTANCE-d CHROMATIC NUMBER as a decision problem

Fix a natural number $d$. The decision problem DISTANCE-$d$ CHROMATIC NUMBER accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, K)$ (a natural number, a list of pairs of natural numbers and a natural number), to an instance that is well-formed for DISTANCE-$d$ CHROMATIC NUMBER and feasible for DISTANCE-$d$ CHROMATIC NUMBER (with the fixed $d$). It rejects every bitstring that does not decode to such an instance.
