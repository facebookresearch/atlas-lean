# Halting space-bounded runs obey the configuration-count time bound

Let $M$ be a deterministic Turing machine with $k$ work tapes, a finite alphabet $\Sigma$ and a
finite set of states $Q$, let $w$ be an input and $s \in \mathbb{N}$, and suppose that for every
$t$ the computation of $M$ on $w$ visits at most $s$ work-tape cells (summed over the work tapes)
in its first $t$ steps. If $M$ halts on $w$, then $M$ halts on $w$ within
$(|w| + 2)\,(|Q| + 1)\,(2s + 1)^k\,(|\Sigma| + 1)^{2s + k}$ steps.
