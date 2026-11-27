# The class APX

APX is the set of maximization problems $P$ that are NP optimization
problems (feasibility is decidable in polynomial time, and a polynomial-time computable map
sends every instance-solution pair to a signed fraction with nonzero denominator that equals the
objective value whenever the solution is feasible) and for which there are a rational number
$\rho$ with $0 < \rho \le 1$ and a polynomial-time algorithm $A$ achieving ratio $\rho$ on $P$ at
precision $2$: for every instance $x$ and every feasible solution $s$ of $x$, the output $y$ of
$A$ on $x$ and the unary precision string $11$ is a feasible solution of $x$ whose value is at
least $\rho$ times the value of $s$.

## Sources

- C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and complexity classes", Journal of Computer and System Sciences 43 (1991), 425-440.
