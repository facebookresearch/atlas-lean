# Copying a counter through $W$

Let $s$ be a counter, $c$ a stack different from the stack
of $s$ and from $W$, and $x$ a symbol of $c$. Suppose the instruction at label $l_1$ pops the
stack of $s$ until it is empty, pushing $x$ onto $c$ and the unit symbol onto $W$ for each popped
symbol, then goes to $l_2$; and the instruction at $l_2$ pops $W$ until it is empty, pushing the
unit symbol of $s$ onto the stack of $s$ for each popped symbol, then goes to $\ell$. Then for
every $n$, every flag and all stacks $S$ in which the stack of $s$ holds $n$ unit symbols of $s$
and $W$ is empty, the emitter goes from label $l_1$ with stacks $S$ to label $\ell$ in exactly
$2n + 2$ steps, with some flag and the stacks $S$ except that $n$ copies of $x$ are pushed onto
$c$.
