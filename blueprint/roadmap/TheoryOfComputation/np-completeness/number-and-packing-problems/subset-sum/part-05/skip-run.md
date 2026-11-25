# Skipping a number block

Let $p$ and $s$ be lists of bits, and write $\mathrm{delimit}(p)$
for the self-delimiting encoding of $p$ (each bit $b$ written as true followed by $b$, then a
terminating false). Suppose the SUBSET-SUM verifier machine is in the state that skips an
unchosen number block, with flag $z$ recording whether the bits read so far end in false and any
value of its local Boolean variable, with the bits of $\mathrm{delimit}(p)$ followed by the bits
of $s$ on the input stack $X$, arbitrary contents on the stacks $W$, $T$, $A$, $B$, and the
scratch stacks $P$, $Q$ empty. Then after exactly $|p| + 1$ steps the stack $X$ holds the bits of
$s$, all other stacks are unchanged, the local variable is false, and the machine is in its
rejecting state if either $p$ is non-empty and ends in false or $p$ is empty and $z$ is true, and
in the state that starts the next number otherwise.
