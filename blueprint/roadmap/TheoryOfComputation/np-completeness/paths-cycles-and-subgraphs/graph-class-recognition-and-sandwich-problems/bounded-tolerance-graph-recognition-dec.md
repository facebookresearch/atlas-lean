# BOUNDED TOLERANCE GRAPH RECOGNITION as a decision problem

The decision problem BOUNDED TOLERANCE GRAPH RECOGNITION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs $(n, E)$ (a natural number and a list of pairs), to an instance whose edge list has no repeated entries and every pair $(u, v)$ of which satisfies $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$, and which is feasible for BOUNDED TOLERANCE GRAPH RECOGNITION. It rejects every bitstring that does not decode to such an instance.
