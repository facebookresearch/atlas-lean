# CNF expressions equivalent to a relation

A CNF expression whose literals all refer to coordinates below $k$ is equivalent to a stored relation $(k, R)$ when it is satisfied by exactly the tuples $t$ for which $[t(0), \dots, t(k-1)]$ is a row of $R$. Only the length-$k$ rows count: for $(1, [[\,]])$ an unsatisfiable CNF (for instance the empty clause) is equivalent to the relation.
