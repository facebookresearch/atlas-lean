# WEIGHTED INDEPENDENT DOMINATING SET (chordal) as a decision problem

The decision problem WEIGHTED INDEPENDENT DOMINATING SET for chordal graphs accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding (natural numbers in binary), to an instance $(n, E, w, B)$ that is well formed (a simple edge list on $\{0, \dots, n-1\}$, one weight per vertex, chordal graph) and feasible (some independent dominating set has total weight at most $B$). It rejects every bitstring that does not decode to an instance.
