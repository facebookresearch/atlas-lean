# SHORTEST COMMON SUPERSTRING FOR SHORT REPETITION-FREE STRINGS as a decision problem

The decision problem SHORTEST COMMON SUPERSTRING FOR SHORT REPETITION-FREE STRINGS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(k, R, K)$ of an alphabet size, a list of strings and a bound, to an instance that is [well-formed](well-formed-15.md) for SHORTEST COMMON SUPERSTRING FOR SHORT REPETITION-FREE STRINGS and feasible for SHORTEST COMMON SUPERSTRING. It rejects every bitstring that does not decode to such an instance.
