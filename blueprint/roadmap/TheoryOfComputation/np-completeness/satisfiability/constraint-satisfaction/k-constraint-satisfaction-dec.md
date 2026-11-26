# k-CONSTRAINT SATISFACTION as a decision problem

Fix a natural number $k$. The decision problem k-CONSTRAINT SATISFACTION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples of a variable count, a clause list and a bound, to an instance that is [well-formed](well-formed-3-3.md) for $k$ and [feasible](kconstraint-satisfaction-feasible.md) for k-CONSTRAINT SATISFACTION. It rejects every bitstring that does not decode to such an instance.
