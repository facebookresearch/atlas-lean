# MINIMUM INFERRED REGULAR EXPRESSION as a decision problem

The decision problem MINIMUM INFERRED REGULAR EXPRESSION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of quadruples $(k, S, T, K)$, to an instance that is [well-formed](../finite-automata/well-formed-5.md) and [feasible](minimum-inferred-regular-expression-feas.md) for MINIMUM INFERRED REGULAR EXPRESSION. It rejects every bitstring that does not decode to such an instance.
