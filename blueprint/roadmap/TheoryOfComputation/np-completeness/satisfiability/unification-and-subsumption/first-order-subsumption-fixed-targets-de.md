# FIRST ORDER SUBSUMPTION WITH n TARGETS as a decision problem

Fix a natural number $n$. The decision problem FIRST ORDER SUBSUMPTION WITH n TARGETS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of quadruples (function-symbol arities, a variable count, pattern token lists and target token lists), to an instance that is [well-formed](well-formed-4-2.md) for $n$ and feasible for FIRST ORDER SUBSUMPTION. It rejects every bitstring that does not decode to such an instance.
