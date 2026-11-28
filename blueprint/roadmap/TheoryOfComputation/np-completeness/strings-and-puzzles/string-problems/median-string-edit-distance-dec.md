# MEDIAN STRING UNDER EDIT DISTANCE as a decision problem

The decision problem MEDIAN STRING UNDER EDIT DISTANCE accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(|\Sigma|, S, K)$ of an alphabet size, a list of strings and a bound, to an instance that is well-formed and [feasible](median-string-edit-distance-feasible.md) for MEDIAN STRING UNDER EDIT DISTANCE. It rejects every bitstring that does not decode to such an instance.
