# Clause-by-clause translation with a fresh-number counter

For a CNF formula this returns a
pair $(N, \psi)$ of a natural number $N$ and a CNF formula $\psi$. The empty formula gives $N = 0$
and $\psi$ empty. A formula with first clause $C$ and remaining clauses $\varphi'$, whose pair is
$(N', \psi')$, gives $N = N' + \max(|C| - 1, 0)$ and, as $\psi$, the chain of clauses replacing
$C$ with fresh numbers from $N'$ on, followed by the clauses of $\psi'$.

Fresh numbers are thus handed out from the last clause backwards, and $N$ is the next free one.
