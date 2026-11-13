# The idle-extended step is the situation step applied to the stacks

Let $M$ be a finite
TM2 machine and $c$ a configuration with label $l$, state $v$ and stacks $S$, and let
$(l', v', P, n)$ be the situation step of $M$ at label $l$ and state $v$ on the windows of $c$.
Then the idle-extended step of $M$ at $c$ is the configuration with label $l'$, state $v'$ and,
on each stack $k$, the list $P_k$ placed on top of what remains of $S_k$ after removing its top
$n_k$ symbols.

This is an equality of full configurations and needs no bound on the stack heights.
