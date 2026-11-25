# Program of the PARTITION doubling machine

The program of the doubling machine, a multi-stack Turing machine with the
[stacks](k.md) $X$, $R$, $O$ and Boolean internal state. At $\mathsf{scan}(q)$, if $X$ is empty
it goes to $\mathsf{emit}$; otherwise it pops the top bit $b$ of $X$, pushes the
[output bits](chunk.md) for $b$ in phase $q$ onto $R$ one after the other (the last one on top)
and goes to $\mathsf{scan}(q')$, where $q'$ is the [next phase](next.md) after $b$. At
$\mathsf{emit}$ it moves the bits of $R$ onto $O$ one at a time, then goes to $\mathsf{done}$.
At $\mathsf{done}$ it halts.
