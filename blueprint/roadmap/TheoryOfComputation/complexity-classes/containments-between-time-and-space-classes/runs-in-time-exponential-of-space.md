# Exponential time bound from a space bound and halting

Let $M$ be a deterministic Turing machine with $k$ work tapes, a finite alphabet $\Sigma$ and a
finite set of states $Q$, let $w$ be an input and $s \in \mathbb{N}$. If every computation of $M$
on $w$ visits at most $s$ work-tape cells (summed over the work tapes) and $M$ halts on $w$, then
$M$ halts on $w$ within

$$
(|w| + 2) \cdot (|Q| + 1)\, 2^{(|\Sigma| + 1) k + k} \cdot 2^{(2(|\Sigma| + 1) + k)\, s}
$$

steps.
