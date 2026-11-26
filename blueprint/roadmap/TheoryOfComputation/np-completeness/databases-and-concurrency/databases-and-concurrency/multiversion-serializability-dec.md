# MULTIVERSION SERIALIZABILITY as a decision problem

The decision problem MULTIVERSION SERIALIZABILITY accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a transaction count and a schedule, to an instance that is [well-formed](well-formed-11.md) and [feasible](multiversion-serializability-feasible.md) for MULTIVERSION SERIALIZABILITY. It rejects every bitstring that does not decode to such an instance.
