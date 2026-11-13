# Embedding the first machine's configurations into a composite

Let $M_1$ and $M_2$ be
single-tape Turing machines over the same alphabet, and let $M$ be their composite, whose states
are the disjoint union of those of $M_1$ and of $M_2$: $M$ starts in the start state of $M_1$ and
runs $M_1$, where $M_1$ would halt it enters the start state of $M_2$ instead, and it then runs
$M_2$ and halts where $M_2$ halts. A configuration of $M_1$ with tape $t$ is sent to the
configuration of $M$ with the same tape $t$ whose state is the copy of $q$ if $M_1$ is in state
$q$, and the start state of $M_2$ if $M_1$ has halted.

## Sources

- public version of upstream CSLib's private `toCompCfg_left`.
