# The original machine simulates the restricted one step for step

Let $S$ be a set of states
supporting a single-tape Turing machine $M$, and relate a configuration of the restriction of $M$
to $S$ to the configuration of $M$ with the same state, viewed as a state of $M$, and the same
tape. Suppose the configuration $c$ of the restricted machine is related to the configuration $d$
of $M$. If the restricted machine steps from $c$ to $c'$, then $M$ reaches, in one or more steps
from $d$, the configuration related to $c'$. If the restricted machine has no step from $c$, then
$M$ has no step from $d$.
