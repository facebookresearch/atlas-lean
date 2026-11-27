# Correctness of the witness formula check

Let $N$ be a list of natural numbers, $w$ a list
of booleans and $\varphi$ a CNF formula. The check of $\varphi$ against $N$ and $w$ returns true if
and only if $\varphi$ is satisfied by the assignment that sends each natural number $x$ to the value
returned by looking up $x$ in $N$ and $w$.
