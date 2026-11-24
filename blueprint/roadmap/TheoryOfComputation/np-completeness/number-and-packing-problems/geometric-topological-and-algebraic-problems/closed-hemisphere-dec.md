# CLOSED HEMISPHERE as a decision problem

The decision problem CLOSED HEMISPHERE accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(m, X, K)$ of a tuple length, a list of integer tuples and a bound, to an instance that is well-formed for OPEN HEMISPHERE (every element of $X$ is an $m$-tuple, the tuples are pairwise distinct, and $0 < K \le |X|$) and feasible for CLOSED HEMISPHERE. It rejects every bitstring that does not decode to such an instance.
