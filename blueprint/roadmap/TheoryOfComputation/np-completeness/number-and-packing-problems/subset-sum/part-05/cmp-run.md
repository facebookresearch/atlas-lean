# Comparing the sum with the target

Let $s$ and $\tau$ be bit lists. Start the SUBSET-SUM
verifier machine at the comparison label, with any value of the local variable, symbol lists $x$
and $w$ on $X$ and $W$, the target $\tau$ on $T$ and the sum $s$ on $B$ (both as bit symbols, last
bit on top), and the stacks $A$, $P$ and $Q$ empty. Then within $|s| + 1$ steps the machine reaches
the accepting label if $s = \tau$ and the rejecting label otherwise.
