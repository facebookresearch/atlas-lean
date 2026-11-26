# Moving a table marker between stacks

For stacks $a$ and $b$, a label $e$ and a map $f$
from symbols to labels, this machine instruction does the following: if the top of $a$ is a table
marker $y$ (that is, $\mathsf{dead}$ or $\mathsf{val}(c)$ for a bit $c$), it pops $y$ from $a$,
pushes it onto $b$ and goes to $f(y)$; if $a$ is empty or has another symbol on top, it goes to
$e$ and leaves the stacks unchanged.

The invariants of the lookup machine rule out another symbol on top of $a$.
