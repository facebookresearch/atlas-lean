# From 3-SAT to constraint graphs over an eight-letter alphabet

For a 3-CNF formula $\varphi$ with $m$ clauses there is a polynomial-time constructible binary constraint graph $G_\varphi$ over the alphabet $\{0,1\}^3$ with one vertex per variable, one vertex per clause and $3m$ edges, such that $G_\varphi$ is satisfiable iff $\varphi$ is satisfiable, and

$$\mathrm{UNSAT}(G_\varphi) \ge \frac{1}{3} \min_{a} \frac{\#\{\text{clauses of } \varphi \text{ falsified by } a\}}{m}.$$

In particular, if $\varphi$ is unsatisfiable then $\mathrm{UNSAT}(G_\varphi) \ge 1/(3m)$.

## Proof sketch

A clause vertex carries the values of its three literals and the edge to each variable vertex requires that the clause is satisfied and that the claimed bit agrees with the variable's label. A labelling decodes to the assignment on the variable vertices; every clause it falsifies has at least one violated edge among its three.

## Depends on

- [Assignment testers](../pcp-constructions/assignment-testers.md)
- [Cook–Levin theorem: SAT is NP-complete](../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007.
