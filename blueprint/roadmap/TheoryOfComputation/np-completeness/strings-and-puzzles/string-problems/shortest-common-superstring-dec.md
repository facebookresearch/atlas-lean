# SHORTEST COMMON SUPERSTRING as a decision problem

The decision problem SHORTEST COMMON SUPERSTRING accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(k, R, K)$ of an alphabet size, a list of strings and a bound, to an instance that is [well-formed](well-formed-16.md) and [feasible](shortest-common-superstring-feasible.md) for SHORTEST COMMON SUPERSTRING. It rejects every bitstring that does not decode to such an instance.
