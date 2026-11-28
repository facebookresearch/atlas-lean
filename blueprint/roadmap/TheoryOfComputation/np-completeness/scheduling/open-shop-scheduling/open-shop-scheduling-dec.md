# OPEN-SHOP SCHEDULING as a decision problem

The decision problem OPEN-SHOP SCHEDULING accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(m, J, D)$ (a natural number, a list of lists of natural numbers and a natural number), to an instance that is well-formed ($m > 0$, every job has exactly $m$ tasks, and the last component is positive) and feasible for OPEN-SHOP SCHEDULING. It rejects every bitstring that does not decode to such an instance.
