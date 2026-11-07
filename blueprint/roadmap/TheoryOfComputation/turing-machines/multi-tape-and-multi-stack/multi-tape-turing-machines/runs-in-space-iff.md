# Relabelling preserves space bounds

Let $M$ and $M'$ be multi-tape Turing machines with
the same number of work tapes and the same alphabet such that $M'$ simulates $M$ up to a state
relabelling $f$. Then for every input $x$ and every $s \in \mathbb{N}$, $M'$ runs in space $s$
on $x$ if and only if $M$ runs in space $s$ on $x$.
