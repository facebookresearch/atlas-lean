# Uniform constants for the exponential time-from-space bound

Let $M$ be a deterministic multi-tape Turing machine with a finite alphabet and finitely many
states. There are natural numbers $a$ and $c$ such that for every input $w$ and every
$s \in \mathbb{N}$: if every computation of $M$ on $w$ visits at most $s$ work-tape cells (summed
over the work tapes) and $M$ halts on $w$, then $M$ halts on $w$ within
$(|w| + 2) \cdot a \cdot 2^{cs}$ steps.

The constants depend only on $M$, not on the input or the space bound.
