# Deciding by a code is finite-state decidability

Let $c$ be a code with $k$ work tapes,
let $L$ be a set of binary words, and let $t$ and $s$ map binary words to natural numbers. If
the machine of $c$ decides $L$, that is, started on any binary word $w$ it halts with the one-bit
output $\mathrm{true}$ if $w \in L$ and $\mathrm{false}$ otherwise, and if on every binary word
$w$ it halts within $t(w)$ steps and visits at most $s(w)$ work-tape cells, then some binary
multi-tape machine with finitely many states decides $L$ within the same bounds.
