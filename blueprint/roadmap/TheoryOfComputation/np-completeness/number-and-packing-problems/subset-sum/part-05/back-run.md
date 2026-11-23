# Moving the new sum back

Let $\mathit{res}$ be a bit list. Start the SUBSET-SUM verifier
machine at the label that moves the new sum back, with any value of the local variable, symbol lists
$x$, $w$, $t$ on $X$, $W$, $T$, the sum stack $A$ empty, $\mathit{res}$ (as bit symbols, last bit
on top) on $B$, and the scratch stacks $P$ and $Q$ empty. Then after exactly
$|\mathit{res}| + 1$ steps the machine is at the label that starts the next number, with some value
of the local variable, $x$, $w$, $t$ unchanged, $\mathit{res}$ (as bit symbols, first bit on top)
on $A$, and $B$, $P$, $Q$ empty.
