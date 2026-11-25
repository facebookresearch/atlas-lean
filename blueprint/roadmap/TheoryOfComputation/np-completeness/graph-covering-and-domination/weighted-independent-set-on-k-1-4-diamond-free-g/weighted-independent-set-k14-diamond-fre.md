# Weighted independent set on $K_{1,4}$- and diamond-free graphs (decision)

The decision problem WEIGHTED INDEPENDENT SET on $(K_{1,4}, \text{diamond})$-free graphs accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding (natural numbers in binary), to an instance $(n, E, w, k)$ that is well formed (a simple edge list on $\{0, \dots, n-1\}$, one weight per vertex, no induced $K_{1,4}$ and no induced diamond) and feasible (some independent set has total weight at least $k$). It rejects every bitstring that does not decode to an instance.
