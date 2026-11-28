# DOUBLE DIGEST as a decision problem

The decision problem DOUBLE DIGEST accepts a bitstring $x$ exactly when $x$ decodes, under the
canonical bitstring encoding of DOUBLE DIGEST instances, to an instance that is
[well-formed](well-formed.md) and [feasible](double-digest-feasible.md). It rejects every
bitstring that does not decode to an instance.
