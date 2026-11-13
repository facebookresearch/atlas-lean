# Single-tape emulation of halting multi-stack runs

Let $M$ be a bundled multi-stack
machine with emulation constant $C$, and $L$ an input for its input stack. If $M$, started on
$L$, reaches after $t$ steps a configuration $c$ from which it does not step, then the
single-tape emulation of $M$, started on the encoding of $L$, reaches in some number
$n \le C t (|L| + C t + 1)$ of steps a configuration from which it does not step. That
configuration is the single-tape form of a configuration of the $\mathrm{TM1}$ emulator of $M$
that represents $c$: it has the corresponding label and the same internal state, and its head
is at the bottom marker of a tape whose $k$-th track lists the $k$-th stack of $c$ from bottom
to top.
