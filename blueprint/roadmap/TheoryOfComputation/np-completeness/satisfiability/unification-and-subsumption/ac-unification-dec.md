# AC-UNIFICATION as a decision problem

The decision problem AC-UNIFICATION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of quintuples (arities, AC symbols, a variable count and two token lists), to an instance that is [well-formed](well-formed.md) and [feasible](acunification-feasible.md) for AC-UNIFICATION. It rejects every bitstring that does not decode to such an instance.
