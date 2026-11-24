# Instruction for reading a unary count

For a stack $k$ of the tokenizer and labels $s$ and
$t$, this is the tokenizer instruction that looks at the top of the formula stack $X$. If it is
the bit true, the instruction pops it, pushes the clause-end symbol $\mathsf{cl}$ onto $k$ and
goes to $s$; if it is the bit false, it pops it and goes to $t$; otherwise, when $X$ is empty or
its top is not a bit, it goes to $\mathsf{rej}$. The internal bit is set to true in the first two
cases and to false in the last.

When $k$ is not $X$ and the instruction is placed at label $s$, a run on a formula stack that
starts with $m$ bits true followed by a bit false pops these $m + 1$ bits, pushes $m$ copies
of $\mathsf{cl}$ onto $k$ and goes to $t$.
