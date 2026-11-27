# Walking a whole clause gives its chain

For every non-empty clause $C$ and every
$z \in \mathbb{N}$, the output clauses of the literals of $C$, walked from its last literal with
counter $z$, with both the first-walked flag and the last-walked flag true, that is,
$\mathrm{walkF}(C, \mathrm{true}, \mathrm{true}, z)$, are the chain of clauses replacing $C$ with
fresh numbers from $z$ on.
