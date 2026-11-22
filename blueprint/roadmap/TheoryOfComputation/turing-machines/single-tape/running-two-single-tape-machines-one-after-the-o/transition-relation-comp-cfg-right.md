# The composite simulates steps of the second machine

Let $M_1$ and $M_2$ be single-tape
Turing machines over the same alphabet, and let $M$ be their composite, whose states are the
disjoint union of those of $M_1$ and of $M_2$: $M$ starts in the start state of $M_1$ and runs
$M_1$, where $M_1$ would halt it enters the start state of $M_2$ instead, and it then runs $M_2$
and halts where $M_2$ halts. Let $\iota_2$ send a configuration of $M_2$ to the configuration of
$M$ with the same tape whose state is the copy of the state of $M_2$, halted if $M_2$ has halted.
If $M_2$ moves from a configuration $c$ to a configuration $c'$ in one step, then $M$ moves from
$\iota_2(c)$ to $\iota_2(c')$ in one step.
