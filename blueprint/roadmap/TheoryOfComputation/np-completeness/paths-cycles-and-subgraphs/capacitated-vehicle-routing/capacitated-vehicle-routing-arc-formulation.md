# Three-index vehicle formulation of capacitated vehicle routing

Let customers $i = 1, \dots, n$ have demands $q_i \ge 0$ (zero allowed), let $0$ be the depot, let vehicles $k = 1, \dots, m$ have capacity $Q \ge 0$, and let $c_{ij}$ be arc costs. Use binary variables $x_{kij}$ (vehicle $k$ traverses arc $(i, j)$, $i \ne j$), $y_{ki}$ (vehicle $k$ serves customer $i$) and $u_k$ (vehicle $k$ is used), with constraints: $\sum_ky_{ki} = 1$ for every customer; $\sum_jx_{kij} = \sum_jx_{kji} = y_{ki}$ for every vehicle and customer; $\sum_jx_{k0j} = \sum_jx_{kj0} = u_k$; $y_{ki} \le u_k$; $\sum_iq_iy_{ki} \le Qu_k$; and, for every vehicle $k$, nonempty set $S$ of customers and $h \in S$, $\sum_{i, j \in S}x_{kij} \le \sum_{i \in S \setminus \{h\}}y_{ki}$. Then the integral solutions correspond to fleets in which each vehicle has either an empty route or one depot-to-depot cycle, every customer is visited exactly once, and every route's load is at most $Q$, with cost $\sum_{k,i,j}c_{ij}x_{kij}$; a single-customer route uses the two arcs $0 \to i \to 0$. The subtour constraints are needed even for zero-demand customers, and a two-index formulation with only subtour constraints does not encode capacity. The linear-relaxation value is a lower bound on the optimal routing cost, not a routing plan.

## Expansion

This statement is not ready: the following prerequisites have no page yet.

- Proof of the route–solution correspondence for the stated subtour constraints.
