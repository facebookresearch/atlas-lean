# Values of the fresh variables in the 3SAT translation

For an assignment
$v : \mathbb{N} \to \mathrm{Bool}$, a CNF formula $\varphi$ and a natural number $w$, the value
$f_v(\varphi, w)$ is defined by recursion on $\varphi$. For the empty formula it is false. For a
formula with first clause $C$ and remaining clauses $\varphi'$, let $N'$ be the next free fresh
number of the clause-by-clause translation of $\varphi'$, and let $k = \max(|C| - 1, 0)$ be the
number of fresh variables reserved for $C$. If $w < N'$, then $f_v(\varphi, w)$ is
$f_v(\varphi', w)$; otherwise $f_v(\varphi, w)$ is true exactly when $v$ satisfies some literal
of the clause obtained from $C$ by dropping its first $N' + k - w$ literals, where the
subtraction is truncated at $0$.

The chain of clauses replacing $C$ uses the fresh numbers $N'$ to $N' + k - 1$, so for these $w$
the value records whether $v$ satisfies one of the last $w - N' + 1$ literals of $C$.
