# TRAVELING REPAIRMAN as a decision problem

The decision problem TRAVELING REPAIRMAN accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of quadruples $(n, t, s, K)$ of a number of locations, a distance matrix, a start and a bound, to an instance that is [well-formed](well-formed-6.md) and [feasible](traveling-repairman-feasible.md) for TRAVELING REPAIRMAN. It rejects every bitstring that does not decode to such an instance.
