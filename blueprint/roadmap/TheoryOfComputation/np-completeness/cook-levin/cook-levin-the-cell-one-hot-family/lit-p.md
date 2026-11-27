# One-hot generator: the routine for one literal

Let $L$ be a layout with $g$ symbol codes,
$c$ a clause kind of a cell of $L$ and $l < g$ a literal index, and write $\mathrm{off}_c(l)$ for
the offset of literal $l$ of $c$ from the cell base. The routine for literal $l$ of $c$ is the
following fragment of the one-hot generator for $L$, which acts on unit counters and a Boolean
output stack. It copies the cell base counter $\mathrm{CB}$ onto counter $Q$ (restoring
$\mathrm{CB}$ through the scratch counter $\mathrm{tmp}$) and pushes $\mathrm{off}_c(l)$ more
units onto $Q$, so that $Q = \mathrm{CB} + \mathrm{off}_c(l)$ when $Q$ and $\mathrm{tmp}$ start
empty. Then it repeats: pop one unit from counter $P$, halting if $P$ is empty; compare $P$ with
$Q$ by popping both in step onto the scratch counters $c_1$ and $c_2$, then move those units back;
if $P \ne Q$, prepend the gap block $01$ to the output and repeat. Once $P = Q$, it prepends the
two-bit slot encoding of the sign of $c$ ($10$ if positive, $11$ if negative) to the output,
empties $Q$, and goes to the routine for literal $l - 1$ of $c$, or to the end of clause $c$ when
$l = 0$.
