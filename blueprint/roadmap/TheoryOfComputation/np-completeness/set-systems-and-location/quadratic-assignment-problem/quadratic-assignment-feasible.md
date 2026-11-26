# Feasible quadratic assignment instances

An instance $(n, F, D, K)$ of quadratic
assignment is feasible when there is a permutation $\pi$ of the numbers $0, \dots, n - 1$ such
that

$$
\sum_{a < n} \sum_{b < n} F_{a b} \, D_{\pi(a) \pi(b)} \le K.
$$

Here $F_{a b}$ is entry $b$ of row $a$ of $F$, and likewise for $D$; an entry that is missing,
because the matrix has too few rows or the row is too short, is read as $0$.
