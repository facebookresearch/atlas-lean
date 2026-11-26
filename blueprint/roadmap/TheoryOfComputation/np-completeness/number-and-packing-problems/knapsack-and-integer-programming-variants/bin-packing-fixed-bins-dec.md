# BIN PACKING WITH K BINS as a decision problem

Fix a natural number $K$. The decision problem BIN PACKING WITH K BINS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a list of sizes and a capacity, to an instance that is [well-formed](well-formed.md) and [feasible](../bin-packing/bin-packing-feasible.md) for BIN PACKING with $K$ bins. It rejects every bitstring that does not decode to such an instance.
