# One step of the wrapped machine

For a partial recursive code $c$, the step function of the
wrapped machine for $c$ is Mathlib's multi-stack (TM2) step function for the program of the
wrapped machine for $c$. It sends a configuration without a current label (a halted one) to
none, and a configuration with current label $l$ to the configuration obtained by executing the
statement that the program assigns to $l$ on its internal state and stacks.
