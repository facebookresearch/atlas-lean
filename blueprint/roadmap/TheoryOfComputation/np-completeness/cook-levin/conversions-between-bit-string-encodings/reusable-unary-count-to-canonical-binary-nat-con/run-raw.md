# Converter turns a unary count into a raw canonical binary payload

Let $n$ be a natural number, $o$ a bit string, $v$ a Boolean and $S$ stack contents of the [unary-to-binary
converter](prog.md) in which stack $A$ holds $n$ copies of the counter symbol, stacks $H$, $T$ and $X$ are empty and
the output stack $O$ holds $o$. Then there are an internal state $w$ and stack contents $U$ such that the unframed
converter goes from label $\mathrm{emit}(\mathrm{hv})$, internal state $v$ and stacks $S$ to label done, internal
state $w$ and stacks $U$ in at most $710n + 306$ steps, where $U_O$ is the binary code of $n$ (least significant bit
first, no trailing zero) followed by $o$, the stacks $A$, $H$, $T$, $X$ are empty in $U$, and every other stack is
the same in $U$ as in $S$.
