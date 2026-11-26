# Certificates compose under binary operations

If $S_1$ certifies the value of $f_1$ at $x$ and $S_2$ certifies the value of $f_2$ at $x$, then $S_1 \cup S_2$ certifies the value of $h(f_1, f_2)$ at $x$ for every binary operation $h$. Hence $C(h(f_1, f_2), x) \le C(f_1, x) + C(f_2, x)$ for every input $x$.

## Proof sketch

Every input agreeing with $x$ on $S_1 \cup S_2$ has the same values of $f_1$ and $f_2$ as $x$, hence the same value of $h(f_1, f_2)$.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
