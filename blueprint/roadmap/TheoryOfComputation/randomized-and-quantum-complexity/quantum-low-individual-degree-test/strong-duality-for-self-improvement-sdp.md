# Strong duality for the self-improvement semidefinite program

For a family of point effects $\{A^u_a\}$ on a finite-dimensional space, consider the primal problem of maximizing $\sum_g \mathrm{tr}(G_g M_g)$ over polynomial submeasurements $\{G_g\}$ (positive operators with $\sum_g G_g \le 1$), where $M_g = \mathbb{E}_u A^u_{g(u)}$ is the uniform average of the point effects for the values of $g$, and the dual problem of minimizing $\mathrm{tr}(Z)$ over operators $Z \ge M_g$ for all $g$. The two optima are equal and attained, the optimal primal has no failure mass, and complementary slackness $G_g (Z - M_g) = 0$ holds for every $g$.

## Proof sketch

Both programs are finite-dimensional and strictly feasible (take $Z$ a large multiple of the identity), so Slater's condition gives strong duality and attainment; complementary slackness follows from equality of the objectives.

## Depends on

- [The low individual degree test](the-low-individual-degree-test.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum Soundness of the Classical Low Individual Degree Test", arXiv:2009.12982, 2020.
