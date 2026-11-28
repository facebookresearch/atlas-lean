# VIEW SERIALIZABILITY as a decision problem

The decision problem VIEW SERIALIZABILITY accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a transaction count and a schedule, to an instance that is well-formed for MULTIVERSION SERIALIZABILITY and [feasible](view-serializability-feasible.md) for VIEW SERIALIZABILITY. It rejects every bitstring that does not decode to such an instance.
