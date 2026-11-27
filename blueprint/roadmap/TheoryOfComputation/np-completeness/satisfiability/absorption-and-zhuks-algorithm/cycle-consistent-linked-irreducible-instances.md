# Cycle-consistent, linked and irreducible CSP instances

Consider a CSP instance $\Theta$ with variables $x_1,\dots,x_n$, domains $D_i\subseteq A$ and constraints $C=((y_1,\dots,y_t);\rho)$. A **path** $z_1-C_1-z_2-\dots-C_{l-1}-z_l$ is a sequence with $z_j,z_{j+1}$ in the scope of $C_j$; it **connects** $b$ and $c$ if there are $a_j\in D_{z_j}$ with $a_1=b$, $a_l=c$ and $(a_j,a_{j+1})$ in the projection of $C_j$ onto $(z_j,z_{j+1})$.

- $\Theta$ is **cycle-consistent** if every constraint is subdirect (1-consistency) and for every $i$ and $a\in D_i$, every path starting and ending at $x_i$ connects $a$ to $a$.
- $\Theta$ is **linked** if for every variable $x_i$ occurring in a constraint and all $a,b\in D_i$ some path starting and ending at $x_i$ connects $a$ and $b$.
- $\Theta$ is **fragmented** if its variable set splits into two disjoint parts, each containing a variable from the scope of some constraint, with every constraint scope inside one part.
- $\Theta$ is **irreducible** if every instance $\Theta'$ whose variables form a subset of $\{x_1,\dots,x_n\}$, with the same domains $D_i$, and each of whose constraints is a projection of some constraint of $\Theta$ onto some set of variables, is fragmented, linked, or has a subdirect solution set.

A constraint $((y_1,\dots,y_t);\rho_1)$ is **weaker** than $((z_1,\dots,z_s);\rho_2)$ if $\{y_i\}\subseteq\{z_j\}$, $\rho_2$ implies $\rho_1$, and $\rho_1$ does not imply $\rho_2$. Within Zhuk's algorithm, for templates with a weak near-unanimity polymorphism, cycle-consistency and irreducibility are enforced in polynomial time, shrinking domains, without losing solutions.

## Depends on

- [Finite relational templates and the homomorphism problem CSP(A)](../finite-domain-csp-dichotomy/finite-templates-and-csp-of-a.md)

## Sources

- Dmitriy Zhuk, "A Proof of the CSP Dichotomy Conjecture", FOCS (2017); Journal of the ACM (2020), arXiv:1704.01914.
