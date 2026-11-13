# Decidability within time and space bounds, unfolded

Let $L$ be a language of Boolean
strings and let $t$ and $s$ assign a natural number to every Boolean string. Then $L$ is decidable
within time $t$ and space $s$ in CSLib's sense, with the identity encoding of inputs, if and only
if there are a number $k$, a finite type of states and a deterministic Turing machine with $k$
work tapes over the Boolean alphabet that decides $L$ and, on every input $w$, runs in time $t(w)$
(every computation path of at least $t(w)$ steps ends in a halted configuration) and in space
$s(w)$ (every computation path visits at most $s(w)$ work-tape cells, summed over the work
tapes).
