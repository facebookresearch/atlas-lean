# H-COLORING as a decision problem

Fix a pattern graph $H = (m, hs)$. The decision problem H-COLORING accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs $(n, E)$ (a natural number and a list of pairs), to an instance that is accepted by GRAPH HOMOMORPHISM on the instance with source $G$ and target $H$ (well-formed and admitting a homomorphism $G \to H$). It rejects every bitstring that does not decode to such an instance.
