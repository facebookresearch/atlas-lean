# Feasible MATRIX COVER instances

A MATRIX COVER instance $(n, A, K)$ is feasible when some sign function
$f : \{0, \dots, n - 1\} \to \{-1, +1\}$ satisfies $\sum_{r, c < n} A_{rc} f(r) f(c) \le K$,
where $K$ is the integer $K_1 - K_2$ encoded by the pair $(K_1, K_2)$ and an entry missing from
the row list of $A$ counts as $0$.
