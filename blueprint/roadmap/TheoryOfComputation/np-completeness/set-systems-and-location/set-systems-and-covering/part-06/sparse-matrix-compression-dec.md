# SPARSE MATRIX COMPRESSION as a decision problem

The decision problem SPARSE MATRIX COMPRESSION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, A, K)$, to an instance that is [well-formed](../part-09/well-formed-5-3.md) and [feasible](sparse-matrix-compression-feasible.md) for SPARSE MATRIX COMPRESSION. It rejects every bitstring that does not decode to such an instance.
