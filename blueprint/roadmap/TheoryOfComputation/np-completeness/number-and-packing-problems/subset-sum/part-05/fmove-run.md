# Moving the final sum for the comparison

Let $x$, $w$, $t$ be lists of stack symbols, $s$
a list of bits and $v$ a Boolean. Started at label $\mathrm{fmove}$ with variable $v$, with $x$,
$w$, $t$ on the stacks $X$, $W$, $T$, the bits of $s$ on $A$ (first bit on top) and $B$, $P$, $Q$
empty, the verifier takes exactly $|s| + 1$ steps to reach label $\mathrm{cmp}$, with some value
of the variable, where $X$, $W$, $T$ are unchanged, $A$, $P$, $Q$ are empty, and $B$ holds the
bits of $s$, last bit on top.
