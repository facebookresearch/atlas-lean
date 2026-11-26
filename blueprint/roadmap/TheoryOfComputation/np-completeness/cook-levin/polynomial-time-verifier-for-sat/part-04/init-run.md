# Initialization step of the lookup machine

Let $t$ and $b$ be lists of symbols and $v$ a
bit. In exactly one step, the lookup program goes from the label $\mathsf{init}$ with internal bit
$v$, stack $T$ holding $t$, stack $B$ holding $b$ and the stacks $S$, $A$, $C$, $V$ empty, to the
label $\mathsf{scan}$ with internal bit $v$, the same contents of $T$, $B$, $S$, $A$ and $C$, and
stack $V$ holding the single symbol name bit false.
