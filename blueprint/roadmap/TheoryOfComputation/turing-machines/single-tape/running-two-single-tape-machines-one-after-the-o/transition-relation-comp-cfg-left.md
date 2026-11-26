# The composite simulates steps of the first machine

Let $M_1$ and $M_2$ be single-tape
Turing machines over the same alphabet, and let $M$ be their composite, whose states are the
disjoint union of those of $M_1$ and of $M_2$: $M$ starts in the start state of $M_1$ and runs
$M_1$, where $M_1$ would halt it enters the start state of $M_2$ instead, and it then runs $M_2$
and halts where $M_2$ halts. Let $\iota_1$ send a configuration of $M_1$ to the configuration of
$M$ with the same tape whose state is the copy of the state of $M_1$, or the start state of $M_2$
if $M_1$ has halted. If $M_1$ moves from a configuration $c$ to a configuration $c'$ in one step,
then $M$ moves from $\iota_1(c)$ to $\iota_1(c')$ in one step.

## Sources

- upstream CSLib's private `map_toCompCfg_left_step`, stated as a relation.
