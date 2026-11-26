# MINIMUM 3DNF SATISFIABILITY as a decision problem

The decision problem MINIMUM 3DNF SATISFIABILITY accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples of a variable count, a clause list and a bound, to an instance that is [well-formed](well-formed-7.md) and [feasible](minimum3-dnf-satisfiability-feasible.md) for MINIMUM 3DNF SATISFIABILITY. It rejects every bitstring that does not decode to such an instance.
