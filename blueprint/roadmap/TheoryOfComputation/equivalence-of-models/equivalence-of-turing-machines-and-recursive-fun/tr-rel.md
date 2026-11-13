# Simulation relation between the code evaluator and the wrapped machine

A configuration $x$
of Mathlib's code evaluator $\mathrm{tr}$ is related to a configuration $d$ of the wrapped machine
of a code $c$ when $d$ has the same internal state as $x$, the stacks of $d$ are the four stacks
of $x$ together with empty input and output stacks, and the labels correspond: if $x$ has halted
then $d$ is at the first post-phase label, and if $x$ is at a label $l$ then $l$ lies in the
support of $c$ and $d$ is at $l$.
