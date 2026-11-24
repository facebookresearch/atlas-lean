# Decidability over codes

Let $L$ be a set of binary words and let $t$ and $s$ map binary
words to natural numbers. Say a machine decides $L$ within $t$ and $s$ when, started on any
binary word $w$, it halts with the one-bit output $\mathrm{true}$ if $w \in L$ and
$\mathrm{false}$ otherwise, halts within $t(w)$ steps, and visits at most $s(w)$ work-tape cells.
Then some binary multi-tape machine with finitely many states decides $L$ within $t$ and $s$ if
and only if, for some number $k$ of work tapes, the machine of some code with $k$ work tapes
decides $L$ within $t$ and $s$.
