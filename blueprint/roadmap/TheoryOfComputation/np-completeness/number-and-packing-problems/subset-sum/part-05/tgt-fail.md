# The verifier rejects an unterminated target block

Let $r$ be a list of bits that does
not begin with a self-delimiting block, that is, parsing one self-delimiting block off the front
of $r$ fails. Suppose the SUBSET-SUM verifier machine is in its target-reading state, with either
value of the flag $z$ recording whether the bits read so far end in false and either value of its
local Boolean variable, with the bits of $r$ on the input stack $X$, arbitrary contents on the
stacks $W$, $T$, $A$, $B$, and the scratch stacks $P$, $Q$ empty. Then the machine reaches its
rejecting state within $|r| + 1$ steps.
