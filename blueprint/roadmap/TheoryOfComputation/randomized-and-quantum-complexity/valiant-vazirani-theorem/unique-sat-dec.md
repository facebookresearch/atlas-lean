# UniqueSAT with a unary variable count as a decision problem

A bitstring $x$ is a
yes-instance exactly when bitstring decoding of $x$, as a pair of a list of booleans and a CNF
formula, succeeds and returns a pair $(u, \varphi)$ such that, writing $m$ for the length of $u$,
every variable occurring in $\varphi$ is less than $m$ and exactly one assignment of booleans to
the variables $0, \dots, m - 1$ satisfies $\varphi$ once it is extended by assigning false to
every variable $v \ge m$.
