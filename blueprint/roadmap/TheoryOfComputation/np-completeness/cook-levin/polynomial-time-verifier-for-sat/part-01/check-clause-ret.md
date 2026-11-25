# Correctness of the witness clause check

Let $N$ be a list of natural numbers, $w$ a list
of booleans and $C$ a CNF clause. The check of $C$ against $N$ and $w$ returns true if and only
if $C$ is satisfied by the assignment that sends each natural number $x$ to the value returned by
looking up $x$ in $N$ and $w$.
