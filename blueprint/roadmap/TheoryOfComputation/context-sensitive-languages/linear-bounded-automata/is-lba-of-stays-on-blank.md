# A machine that, on a blank cell, writes a blank and does not move is a linear bounded automaton

Let $\Sigma$ be a finite nonempty alphabet and let $T$ be a deterministic single-tape Turing machine over
$\Sigma$ with a finite set of states, whose tape cells hold letters of $\Sigma$ or blanks. Suppose that for
every state $q$, the transition of $T$ from $q$ on a blank cell writes a blank and leaves the head where
it is (the next state, or halting, is arbitrary). Then $T$ is a linear bounded automaton: for every input
word $l$ over $\Sigma$ and every configuration $c$ reachable from the initial configuration on $l$ in
finitely many (possibly zero) steps, the space used by $c$ is at most $|l| + 1$. Here the space used by a
configuration is the number of cells from the leftmost to the rightmost of the head cell and the
non-blank cells.

The head never leaves a blank cell, so it stays on the input or on one of the two blank cells next to
it, and non-blank symbols are written only on the input.
