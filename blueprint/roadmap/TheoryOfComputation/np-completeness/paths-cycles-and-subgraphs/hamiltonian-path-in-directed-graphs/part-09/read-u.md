# The unary reader of the Hamiltonian path verifier

For stacks $\mathsf{src}$ and $c$ and
labels $\ell$ (its own) and $m$ (the next one), the statement that goes to label $\mathrm{no}$
if $\mathsf{src}$ is empty; otherwise it pops the top symbol of $\mathsf{src}$ and, if that
symbol is the bit `true`, pushes the bit `true` (one unit) onto $c$ and goes to $\ell$, while
if it is anything else it goes to $m$. Each of the two tests also stores its outcome in the
Boolean variable.

Run in a loop at $\ell$, it reads a unary number off $\mathsf{src}$ onto the counter $c$ and
consumes the terminator.
