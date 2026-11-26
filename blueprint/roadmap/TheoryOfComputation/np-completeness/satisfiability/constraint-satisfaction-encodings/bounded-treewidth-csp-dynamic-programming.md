# CSPs of bounded treewidth are solvable by dynamic programming

Given a CSP instance $F$ over a domain of size $q$ and a nice tree decomposition of its primal graph of width $w$ with $O(|V|)$ nodes, satisfiability, the number of solutions and the weighted partition function of $F$ can be computed with $O(q^{w+1} \cdot \mathrm{poly}(|F|))$ arithmetic operations. The invariant at a node $t$ is the table assigning to each assignment of the bag $B_t$ the number (or weighted sum) of extensions to the variables of the subtree below $t$ satisfying all constraints whose scopes are assigned to that subtree.

## Proof sketch

Introduce, forget and join nodes update the table by extension, summation over the forgotten variable and pointwise product respectively; each constraint is assigned to a node whose bag contains its scope, which exists because scopes are cliques.

## Depends on

- [Primal graph of a CSP instance](primal-graph-of-a-csp.md)
- [Partition function of a weighted CSP](../../../counting-complexity/weighted-csp-partition-functions/partition-function-of-a-weighted-csp.md)

## Sources

- M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, Parameterized Algorithms, Springer, 2015.
