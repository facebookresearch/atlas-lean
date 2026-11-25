# Halting from a configuration is invariant along a run

Let $M$ be a single-tape Turing
machine and let $a$ and $b$ be configurations of $M$ such that the run of $M$ from $a$ reaches $b$
in finitely many steps (possibly none). Then $M$ halts from $a$ if and only if $M$ halts from $b$.

The backward direction holds for any relation; the forward direction uses that $M$ is
deterministic.
