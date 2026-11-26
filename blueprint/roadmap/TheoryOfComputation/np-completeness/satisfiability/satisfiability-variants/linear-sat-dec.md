# LINEAR SAT as a decision problem

The decision problem LINEAR SAT accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a variable count and a CNF formula, to an instance that is [well-formed](well-formed-6.md) and [feasible](../3-sat-with-bounded-occurrences/bounded-occurrence-three-sat-feasible.md) for LINEAR SAT. It rejects every bitstring that does not decode to such an instance.
