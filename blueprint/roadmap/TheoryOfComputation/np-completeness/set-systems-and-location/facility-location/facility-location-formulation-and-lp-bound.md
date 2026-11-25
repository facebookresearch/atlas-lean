# Formulation and LP lower bound for uncapacitated facility location

Let finitely many facilities $i$ (possibly none) have real opening costs $f_i \ge 0$ and finitely many customers $j$, at least one, have real assignment costs $c_{ij} \ge 0$. With no facilities no customer can be assigned, the formulation is infeasible and its optimal cost is $+\infty$ by convention; assume from now on that there is at least one facility. The points with $y_i \in \{0, 1\}$, $x_{ij} \in \{0, 1\}$, $\sum_ix_{ij} = 1$ and $x_{ij} \le y_i$ correspond to choices of a set of open facilities together with an assignment of each customer to an open facility, with cost $\sum_if_iy_i + \sum_{i,j}c_{ij}x_{ij}$; when costs are nonnegative, relaxing $x_{ij}$ to $[0, 1]$ with $y$ binary does not change the optimum. For the linear relaxation with $0 \le x_{ij} \le y_i \le 1$, every dual feasible solution gives a lower bound on the optimal cost, so its value together with any integral solution bounds that solution's suboptimality. No approximation guarantee is claimed.

## Proof depends on

- [Weak duality](../../../../Analysis/convex-analysis-and-variations/lagrange-duality/dual-value-le-primal-value.md): weak duality for the linear relaxation.

## Sources

- D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge University Press, 2011, <https://www.designofapproxalgs.com/>, §4.5 (uncapacitated facility location)
