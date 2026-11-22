# Formula check against a witness

Given a list $N$ of natural numbers, a list $w$ of
booleans and a CNF formula $\varphi$, the check of $\varphi$ against $N$ and $w$ is the timed
computation that runs the clause check against $N$ and $w$ on the clauses of $\varphi$ in order,
adding up their costs, and returns false as soon as one of them returns false. If every clause
check returns true, in particular if $\varphi$ has no clauses, it returns true.
