# Factored tensor network with shape parameter

A factored tensor network on a finite linearly ordered vertex set $J$ has shape parameter
$P \in \mathbb{N}$ when

- every vertex $a$ has at most $2^P$ allowed states;
- capacities are symmetric: $c_{a,b} = c_{b,a}$ for all $a, b$;
- at every vertex $a$, $\sum_{b \ne a} c_{a,b} \le P$;
- for all distinct $a, b$, the label set of $\{a, b\}$ has at most $2^{c_{a,b}}$ elements.
