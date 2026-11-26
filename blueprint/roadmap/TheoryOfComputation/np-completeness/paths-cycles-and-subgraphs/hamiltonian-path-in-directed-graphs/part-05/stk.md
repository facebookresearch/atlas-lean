# Stacks of a quiescent emitter state

In a quiescent state $s$, the stacks $T$, $O$, $F$,
$V$, $W$, $G$ and $X$ hold the lists that $s$ records for them; the stack $Q$ holds the edge
bits of $s$ as bit symbols, reversed so that the last bit is on top; each counter stack $C$,
$M$, $P$, $N$, $R$, $L$, $J$, $D$ holds as many copies of the symbol $\mathrm{cl}$ as the
value that $s$ records for the corresponding counter (the clause count, the counter reserved
for three times the clause count, the diamond top, the row end, the row vertex, the row loop
index, the clause index and the detour vertex), with no relation imposed between these values;
and the scratch stacks $Y$ and $Z$ are empty.
