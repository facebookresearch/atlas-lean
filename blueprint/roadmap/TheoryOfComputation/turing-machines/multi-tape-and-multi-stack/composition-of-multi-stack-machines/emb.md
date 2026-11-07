# Embedding of $M_1$'s configurations into the composite machine

A configuration $c$ of $M_1$
is sent to the configuration of the composite of $M_1$ and $M_2$ whose label is the label of $c$
viewed as a label of the $M_1$ part, or the label that pops $M_1$'s output stack (the start of the
first copy loop) if $c$ is halted, whose state is $(v, q_2, \mathrm{none})$ with $v$ the state of
$c$ and $q_2$ the initial state of $M_2$, and whose stacks are the stacks of $c$ on $M_1$'s stacks,
with $M_2$'s stacks and the scratch stack empty.
