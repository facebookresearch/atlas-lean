# Output clauses of a walked list of literals

For a list $L$ of literals of a clause,
Booleans $f$ and $g$, and $z \in \mathbb{N}$, $\mathrm{walkF}(L, f, g, z)$ is the list of output
clauses of the literals of $L$, in reading order, when $L$ is walked from its last literal with
counter $z$; $f$ tells whether the last literal of $L$ is the first walked in its clause, and $g$
whether the first literal of $L$ is the last walked. It is defined by recursion on $L$. The empty
list gives no clauses. If $L$ has first literal $l$ and remaining literals $L'$, the first clause
is the output clause of $l$ whose first-walked flag is true exactly when $f$ is true and $L'$ is
empty, whose last-walked flag is $g$, and whose counter is $z + n$, where $n$ is the number of
fresh numbers used up by walking $L'$ ($|L'| - 1$ if $f$ is true, with $0 - 1 = 0$, and $|L'|$
otherwise); it is followed by $\mathrm{walkF}(L', f, \mathrm{false}, z)$.
