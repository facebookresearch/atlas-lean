# A single step of the Hamiltonian-path verifier

Let $l, l'$ be labels, $v$ a flag value
and $S, S'$ assignments of a list of symbols to each stack. If executing the verifier's statement
at $l$ with flag $v$ and stacks $S$ jumps to the label $l'$ and leaves the stacks $S'$, then the
verifier goes in exactly one step from label $l$, flag $v$ and stacks $S$ to label $l'$ and
stacks $S'$, with some flag value.
