# Constant-factor approximable problems

A maximization problem $P$ is in $\mathsf{APX}$
when $P$ is an NPO problem and there are a rational number $\rho$ with $0 < \rho \le 1$ and a
polynomial-time algorithm $A$ such that, for every instance $x$ and every feasible solution $s$
for $x$, the output $A(x, 1^2)$ of $A$ on $x$ with the unary precision tape of length $2$ is a
feasible solution for $x$ whose value is at least $\rho$ times the value of $s$.

The ratio $\rho$ is the fraction of the optimum achieved, the reciprocal of the convention
$\rho \ge 1$ in which the value is at least the optimum divided by $\rho$. The NPO
requirement is part of the class: without it, a problem that is not NPO and has value $0$
everywhere would qualify vacuously.

## Sources

- C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and complexity classes", Journal of Computer and System Sciences 43 (1991), 425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Chapter 11.
