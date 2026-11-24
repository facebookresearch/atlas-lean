# Occurrences of a formula with a first clause

Let $C$ be a clause and $\varphi$ a CNF
formula, and write a literal occurrence as a pair $(i, \ell)$ of a clause index $i$ and a literal
$\ell$. The list of literal occurrences of the formula whose first clause is $C$ and whose
remaining clauses are those of $\varphi$ is the list of $(0, \ell)$ for the literals $\ell$ of $C$
in order, followed by the list of $(i + 1, \ell)$ for the occurrences $(i, \ell)$ of $\varphi$ in
order.
