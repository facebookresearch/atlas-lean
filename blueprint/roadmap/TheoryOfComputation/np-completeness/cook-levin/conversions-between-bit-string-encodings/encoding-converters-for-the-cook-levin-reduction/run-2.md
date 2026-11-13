# Runs of the bit-list decoder

For a natural number $n$ and configurations $c$ and $d$ of
the machine decoding the canonical encoding of a bit list (each an optional label, an optional bit
as internal state and the contents of the three bit stacks), this is the proposition that $n$
steps of its program lead from $c$ to $d$: applying the step function $n$ times to $c$ is defined
at every step (no configuration before the last one is halted) and gives $d$.
