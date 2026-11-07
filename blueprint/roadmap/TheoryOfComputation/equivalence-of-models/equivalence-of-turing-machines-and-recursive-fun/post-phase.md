# Post-phase of the wrapped machine

Let $c$ be a code and $b$ a list of bits of length
$k$, and write $\beta(b)$ for $b$ with each bit $0$ replaced by the symbol bit0 and each bit $1$ by
the symbol bit1 of $\Gamma'$. Started at the adapter label post1 with empty local state, $\beta(b)$
followed by the symbol cons on the main stack and all other stacks empty, the wrapped machine is
after exactly $2(k + 1)$ steps in the halting configuration (no label) with empty local state,
$b$ on the output stack and all other stacks empty.
