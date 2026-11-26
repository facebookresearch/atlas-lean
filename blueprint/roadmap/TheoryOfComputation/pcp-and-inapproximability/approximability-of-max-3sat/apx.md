# Membership in APX

An NPO problem $M$ is in APX when there are a rational number
$\rho \ge 1$ and a polynomial-time computable map $A$ from bitstrings to bitstrings such that, for
every instance $x$, the solution $A(x)$ is feasible for $x$ in $M$ and its value is at least
$\mathrm{opt}_M(x) / \rho$, where $\mathrm{opt}_M(x)$ is the optimum of $M$ on $x$.
