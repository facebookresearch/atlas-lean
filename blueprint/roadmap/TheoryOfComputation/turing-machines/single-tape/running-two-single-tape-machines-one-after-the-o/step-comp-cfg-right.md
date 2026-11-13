# Step function of a composite on configurations of the second machine

Let $M_1$ and $M_2$
be single-tape Turing machines over the same alphabet, and let $M$ be their composite, whose
states are the disjoint union of those of $M_1$ and of $M_2$: $M$ starts in the start state of
$M_1$ and runs $M_1$, where $M_1$ would halt it enters the start state of $M_2$ instead, and it
then runs $M_2$ and halts where $M_2$ halts. Let $\iota_2$ send a configuration of $M_2$ to the
configuration of $M$ with the same tape whose state is the copy of the state of $M_2$, halted if
$M_2$ has halted. For every configuration $c$ of $M_2$: if $M_2$ moves from $c$ to $c'$ in one
step, then $M$ moves from $\iota_2(c)$ to $\iota_2(c')$ in one step, and if $c$ has no successor
in $M_2$, then $\iota_2(c)$ has no successor in $M$.

## Sources

- upstream CSLib's private `map_toCompCfg_right_step`.
