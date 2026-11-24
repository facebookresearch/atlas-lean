# Relabelling preserves time bounds

Let $M$ and $M'$ be multi-tape Turing machines with
the same number of work tapes and the same alphabet such that $M'$ simulates $M$ up to a state
relabelling $f$. Then for every input $x$ and every $t \in \mathbb{N}$, $M'$ runs in time $t$ on
$x$ if and only if $M$ runs in time $t$ on $x$.
