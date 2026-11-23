# Stacks of the CLIQUE verifier

The verifier machine for CLIQUE, INDEPENDENT-SET and
VERTEX-COVER, run on an instance with target size $k$ and $n$ vertices, has six stacks: the
input $X$, the witness $W$, the counter $C$ (holding $k$), the counter $N$ (holding $n$), the
vertex stack $V$ and its scratch stack $T$.
