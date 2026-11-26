# DYNAMIC STORAGE ALLOCATION as a decision problem

The decision problem DYNAMIC STORAGE ALLOCATION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of an item list $(s, r, d)$ and a storage size $D$, to an instance that is [well-formed](../part-08/well-formed-2-3.md) and [feasible](dynamic-storage-allocation-feasible.md) for DYNAMIC STORAGE ALLOCATION. It rejects every bitstring that does not decode to such an instance.
