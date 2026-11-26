# Impagliazzo–Paturi–Zane sparsification and ETH in terms of clauses

For every $k$ and $\varepsilon>0$ there is $c=c(k,\varepsilon)$ such that every $k$-CNF $\varphi$ on $n$ variables is equivalent to a disjunction $\bigvee_{i\le t}\psi_i$ of $t\le 2^{\varepsilon n}$ $k$-CNFs, each with at most $cn$ clauses, computable by a branching procedure in time $2^{\varepsilon n}\mathrm{poly}(n)$. Consequently a $k$-SAT algorithm running in time $2^{\delta m}$ in the number $m$ of clauses yields one running in time $2^{(\varepsilon+c\delta)n}$ in the number of variables, and ETH holds iff 3-SAT is not solvable in time $2^{o(m)}$.

## Proof sketch

Branch on 'sunflowers': if many clauses share a common core (heart), either the core is satisfied (replace the petals by the core) or every petal is; choosing thresholds growing with clause size bounds the depth and the number of leaves, and at each leaf every core has few petals, so each variable occurs in $O(1)$ clauses.

## Depends on

- [The exponents s_k of k-SAT and #k-SAT](k-sat-exponents.md)

## Sources

- Russell Impagliazzo, Ramamohan Paturi and Francis Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 2001.
