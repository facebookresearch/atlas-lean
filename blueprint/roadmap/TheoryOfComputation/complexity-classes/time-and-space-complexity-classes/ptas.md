# The class PTAS

PTAS is the set of optimization problems $P$ that are NPO problems
(feasibility is decidable in polynomial time and the objective value is given by a
polynomial-time computable rational encoding) and that have a polynomial-time approximation
scheme: for every natural number $k \ge 1$ there is a polynomial-time algorithm $A$ such that,
for every instance $x$ and every feasible solution $s$ of $x$, the output of $A$ on $x$ and the
string of $k$ ones is a feasible solution of $x$ whose value is at least $(1 - 1/k)$ times the
value of $s$.

## Sources

- C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and complexity classes", Journal of Computer and System Sciences 43 (1991), 425-440.
