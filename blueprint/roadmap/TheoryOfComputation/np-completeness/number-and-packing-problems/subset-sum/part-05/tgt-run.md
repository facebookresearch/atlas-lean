# Reading the target block

Let $p$ and $s$ be lists of bits, and write $\mathrm{delimit}(p)$
for the self-delimiting encoding of $p$ (each bit $b$ written as true followed by $b$, then a
terminating false). Suppose the SUBSET-SUM verifier machine is in its target-reading state, with
flag $z$ recording whether the bits read so far end in false and any value of its local Boolean
variable, with the bits of $\mathrm{delimit}(p)$ followed by the bits of $s$ on the input stack
$X$, a list $t$ of symbols on the target stack $T$, arbitrary contents on the stacks $W$, $A$, $B$,
and the scratch stacks $P$, $Q$ empty. Then after exactly $|p| + 1$ steps the stack $X$ holds the
bits of $s$, the bits of $p$ have been pushed onto $T$ one at a time (so that $T$ holds, from the
top, the bits of $p$ in reverse order followed by $t$), the stacks $W$, $A$, $B$, $P$, $Q$ are
unchanged, the local variable is false, and the machine is in its rejecting state if either $p$
is non-empty and ends in false or $p$ is empty and $z$ is true, and in the state that starts the
next number otherwise.
