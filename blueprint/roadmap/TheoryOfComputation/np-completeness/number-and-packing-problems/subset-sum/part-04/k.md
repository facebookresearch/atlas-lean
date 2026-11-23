# Stacks of the SUBSET-SUM verifier

The verifier has seven stacks: the input $X$, the
witness $W$, the target $T$ (most significant bit on top), the running sum $A$ (least significant
bit on top), the new sum $B$ (most significant bit on top), and the scratch stacks $P$ and $Q$ of
the final comparison.
