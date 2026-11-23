# Reading a polarity

Let $p$, $v$ be bits, $r$, $w$ bit strings, $t$, $b$ symbol stacks and
$c$, $l$ natural numbers. Started at label $\mathsf{pol}$ with internal bit $v$, the bit $p$
followed by the bits of $r$ on the formula stack $X$, the bits of $w$ on the witness stack $W$, $t$
on the token stack $T$, $b$ on the table stack $B$, clause counter $c$ and literal counter $l$, the
tokenizer moves in exactly one step to label $\mathsf{lits}$ with the bits of $r$ on $X$, the bits
of $w$ after its first on $W$, the polarity marker $\mathsf{lit}(p)$ pushed onto $t$, and the same
counters. If $w$ starts with the bit $w_1$, the internal bit becomes $w_1$ and the marker
$\mathsf{val}(w_1)$ is pushed onto $b$; if $w$ is empty, the internal bit becomes false and the
marker $\mathsf{dead}$ is pushed onto $b$.
