# STRICT SERIALIZABILITY as a decision problem

The decision problem STRICT SERIALIZABILITY accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a transaction count and a step schedule, to an instance that is well-formed and feasible for STRICT SERIALIZABILITY. It rejects every bitstring that does not decode to such an instance.
