# Feasible facility location instances

Let $(o, D, B)$ be a facility location instance
with opening costs $o = (o_0, \dots, o_{n-1})$, assignment-cost rows $D = (D_0, \dots, D_{m-1})$
and budget $B$, and write $D_{c,j}$ for the $j$-th entry of the row $D_c$, read as $0$ when $D_c$
has no $j$-th entry. The instance is feasible when there is a map $\sigma$ from the clients
$\{0, \dots, m-1\}$ to the facilities $\{0, \dots, n-1\}$ such that the opening costs of the
facilities in the image of $\sigma$ plus the assignment costs stay within the budget:
$\sum_{j \in \sigma(\{0, \dots, m-1\})} o_j + \sum_{c=0}^{m-1} D_{c,\sigma(c)} \le B$.
