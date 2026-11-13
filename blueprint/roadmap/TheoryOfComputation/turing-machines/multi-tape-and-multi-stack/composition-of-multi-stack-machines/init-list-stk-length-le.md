# Stacks of the initial configuration are no longer than the input

Let $M$ be a finite
multi-stack Turing machine (Mathlib's TM2 model with finitely many stacks, function labels and
internal states, and a finite input alphabet) with input stack $k_0$, and let $l$ be a list of
symbols from the alphabet of stack $k_0$. Then for every stack $k$ of $M$, the stack $k$ in the
initial configuration of $M$ on input $l$ has length at most the length of $l$.

The initial configuration holds $l$ on stack $k_0$ and leaves every other stack empty.
