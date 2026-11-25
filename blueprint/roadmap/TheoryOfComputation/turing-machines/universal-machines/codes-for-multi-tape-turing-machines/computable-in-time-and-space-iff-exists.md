# Computability over codes

Let $g : \alpha \to \beta$ be a function, let inputs in $\alpha$
and outputs in $\beta$ be encoded by injective maps into binary words, and let
$t, s : \alpha \to \mathbb{N}$. Say a machine computes $g$ within $t$ and $s$ when, started on the
encoding of any input $x$, it halts with the encoding of $g(x)$ as output, halts within $t(x)$
steps, and visits at most $s(x)$ work-tape cells. Then some binary multi-tape machine with
finitely many states computes $g$ within $t$ and $s$ if and only if, for some number $k$ of work
tapes, the machine of some code with $k$ work tapes computes $g$ within $t$ and $s$.
