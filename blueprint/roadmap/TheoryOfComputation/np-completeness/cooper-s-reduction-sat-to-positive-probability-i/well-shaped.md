# Shape of reachable construction states

A state of Cooper's construction is well shaped when every node is a root node or has every row's denominator equal to $1$; the recorded roots use each node index at most once and each variable at most once; and every root node is recorded as the root of some variable. Denominator $1$ alone does not make a table deterministic: a row $(u, 2, 1)$ has denominator $1$. Together with the validity condition $\mathit{num} \le \mathit{den}$ of a well-formed network, a denominator of $1$ makes every row's value $0$ or $1$, so the table is deterministic.
