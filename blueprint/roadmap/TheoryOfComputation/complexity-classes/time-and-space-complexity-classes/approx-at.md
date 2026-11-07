# Approximation ratio at a precision

Let $P$ be a maximization problem with objective
value $\mathrm{val}(x, s)$ for instance $x$ and solution $s$, let $A$ be an algorithm taking a
pair of bitstrings, let $k$ be a natural number and let $\rho$ be a rational number. Then $A$
achieves ratio $\rho$ on $P$ at precision $k$ when, for every instance $x$ and every feasible
solution $s$ of $x$, the output $y = A(x, 1^k)$ of $A$ on $x$ and the unary string $1^k$ of $k$
ones is a feasible solution of $x$ with $\rho \cdot \mathrm{val}(x, s) \le \mathrm{val}(x, y)$.

Since every instance has a feasible solution, the output is then always feasible and worth at
least $\rho$ times the value of every feasible solution. The approximation classes share this
call convention: a fully polynomial-time approximation scheme is one algorithm achieving ratio
$1 - 1/k$ at every precision $k \ge 1$, a polynomial-time approximation scheme has such an
algorithm for each $k \ge 1$ separately, and APX asks for some ratio $\rho$ with $0 < \rho \le 1$
at precision $2$.

## Sources

- C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and complexity classes", Journal of Computer and System Sciences 43 (1991), 425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Chapter 11.
