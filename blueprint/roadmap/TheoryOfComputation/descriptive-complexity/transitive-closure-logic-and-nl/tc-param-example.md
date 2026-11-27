# Example: parameterized transitive closure in FO + TC

The FO + TC formula
$\mathrm{TC}(\varphi; (1), (2))$ of arity $1$ whose body $\varphi$ is
$E(0, 1) \lor (E(0, 2) \land E(2, 1))$, where $E$ is relation symbol $1$ (the edge relation).
In the body, variable $0$ is the source, variable $1$ the target, and variable $2$ is outer
variable $0$, shifted by $2$; the endpoint arguments $1$ and $2$ are outer variables, not
shifted. So the formula expresses that outer variable $2$ is reachable from outer variable $1$
by steps that are either an edge or a path of two edges through outer variable $0$.
