# Binary addition of framed numbers in quadratic time

For all natural numbers $m$, $n$ and every Boolean $v$, let $N$ be the length of the
[framed input](pair-input.md) of $m$ and $n$. The [binary addition machine](prog.md) started at
label $0$ with internal state $v$, with the framed input of $m$ and $n$ on the stack $X$ (as bit
symbols) and every other stack empty, reaches label $3$ in at most $N(2N + 6) + 2N + 8$ steps,
with some internal state, the binary code of $m + n$ (least significant bit first, on top) on the
stack $A$, and every other stack empty.

The bound is quadratic in the length of the input, not in the values of $m$ and $n$.
