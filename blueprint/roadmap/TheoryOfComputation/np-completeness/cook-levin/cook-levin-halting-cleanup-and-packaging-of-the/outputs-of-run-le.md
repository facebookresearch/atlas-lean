# A bounded halting run certifies the output

Let $M$ be a finite TM2 machine, $l$ a list
over its input alphabet, $l'$ a list over its output alphabet and $B \in \mathbb{N}$. If the
program of $M$ goes in at most $B$ steps from the initial configuration on input $l$ (its start
label, its initial state, $l$ on the input stack and every other stack empty) to the halting
configuration with output $l'$ (no label, the initial state, $l'$ on the output stack and every
other stack empty), then $M$ outputs $l'$ on input $l$ within $B$ steps.
