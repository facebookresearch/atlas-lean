# H-DECOMPOSITION as a decision problem

Fix a pattern $(m, hs)$. The decision problem H-DECOMPOSITION for the pattern graph $H$ accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs $(n, E)$, to an instance whose edge list is a simple edge list on $\{0, \dots, n - 1\}$ and whose graph has an $H$-decomposition. It rejects every bitstring that does not decode to such an instance.
