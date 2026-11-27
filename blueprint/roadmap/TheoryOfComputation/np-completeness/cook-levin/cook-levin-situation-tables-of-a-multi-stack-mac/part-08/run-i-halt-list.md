# The idle-extended run stays at the halting configuration

Let $M$ be a machine, $s$ a
word over its input alphabet and $l'$ a list over its output alphabet. Suppose that $M$, started
in the initial configuration on $s$, reaches the halting configuration with output $l'$ (halted,
in the initial state, with $l'$ on the output stack and every other stack empty) in at most $p$
steps. Then for every $T \ge p$, the configuration reached after $T$ steps of the idle-extended
run of $M$ from the initial configuration on $s$ is that halting configuration.
