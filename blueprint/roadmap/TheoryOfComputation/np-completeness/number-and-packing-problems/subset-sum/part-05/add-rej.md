# The verifier rejects a chosen block that ends in false

Let $p$ and $\mathit{rest}$ be bit
lists and $z$ a bit such that $p$ is nonempty and ends in false, or $p$ is empty and $z$ is true
(the flag $z$ records whether the bits of the block read so far end in false). Let $c$ be a bit and
$u$ a bit list. Start the SUBSET-SUM verifier machine at the label that adds a chosen number with
carry $c$ and flag $z$, with any value of the local variable, the self-delimiting encoding of $p$
followed by $\mathit{rest}$ (as bit symbols) on the input stack $X$, any symbol lists on $W$, $T$
and $B$, $u$ (as bit symbols) on the sum stack $A$, and the scratch stacks $P$ and $Q$ empty. Then
the machine reaches the rejecting label within $|p| + 1$ steps.
