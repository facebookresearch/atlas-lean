# Converter turns a unary count into a canonical binary frame

Let $n$ be a natural number, $o$ a bit string, $v$ a Boolean and $S$ stack contents of the [unary-to-binary
converter](prog.md) in which stack $A$ holds $n$ copies of the counter symbol, stacks $H$ and $T$ are empty and the
output stack $O$ holds $o$. Then there are stack contents $U$ such that the framed converter goes from label
$\mathrm{emit}(\mathrm{hv})$, internal state $v$ and stacks $S$ to label done, internal state $0$ (false) and stacks
$U$ in at most $708n + 304$ steps, where $U_O$ is the framed form $1 c_1 \cdots 1 c_j 0$ of the binary code
$c$ of $n$ followed by $o$, the stacks $A$, $H$, $T$ are empty in $U$, and every other stack (including $X$) is the
same in $U$ as in $S$.

The bound is linear in $n$, the length of the unary input, not in the length of its binary code.
