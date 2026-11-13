# The verifier rejects an unterminated chosen block

Let $r$ be a bit list from whose front no
complete self-delimiting block can be parsed, let $c$ and $z$ be bits, and let $u$ be a bit list.
Start the SUBSET-SUM verifier machine at the label that adds a chosen number with carry $c$ and
flag $z$ (the flag records whether the bits of the block read so far end in false), with any value
of the local variable, $r$ (as bit symbols) on the input stack $X$, any symbol lists on $W$, $T$
and $B$, $u$ (as bit symbols) on the sum stack $A$, and the scratch stacks $P$ and $Q$ empty. Then
the machine reaches the rejecting label within $|r| + 1$ steps.
