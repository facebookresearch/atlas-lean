# MINIMUM INFERRED UNION-FREE REGULAR EXPRESSION as a decision problem

The decision problem MINIMUM INFERRED UNION-FREE REGULAR EXPRESSION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of quadruples $(k, S, T, K)$, to an instance that is well-formed for MINIMUM INFERRED REGULAR EXPRESSION and [feasible](minimum-inferred-regular-expression-unio.md) for MINIMUM INFERRED UNION-FREE REGULAR EXPRESSION. It rejects every bitstring that does not decode to such an instance.
