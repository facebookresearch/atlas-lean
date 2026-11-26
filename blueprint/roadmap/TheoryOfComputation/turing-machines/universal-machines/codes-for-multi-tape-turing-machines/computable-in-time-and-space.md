# Computation by a code is finite-state computation

Let $c$ be a code with $k$ work tapes,
let $g : \alpha \to \beta$ be a function, let inputs in $\alpha$ and outputs in $\beta$ be encoded
by injective maps into binary words, and let $t, s : \alpha \to \mathbb{N}$. If the machine of $c$,
started on the encoding of any input $x$, halts with the encoding of $g(x)$ as output, halts
within $t(x)$ steps, and visits at most $s(x)$ work-tape cells, then some binary multi-tape
machine with finitely many states computes $g$ within the same bounds in the same sense.
