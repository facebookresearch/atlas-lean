# Polynomial-time approximation schemes

An optimization problem $P$, with value
$\mathrm{val}(x, s)$ of a solution $s$ for an instance $x$, admits a polynomial-time
approximation scheme when $P$ is an NPO problem and for every integer $k \ge 1$ there is a
polynomial-time computable algorithm $A$ on pairs of bitstrings with the following property:
for every instance $x$ and every feasible solution $s$ for $x$, the output $A(x, 1^k)$ on $x$
and the string $1^k$ of $k$ true bits is a feasible solution for $x$ with
$(1 - 1/k)\,\mathrm{val}(x, s) \le \mathrm{val}(x, A(x, 1^k))$. That is, $A$ achieves
approximation ratio $1 - 1/k$, an error of $\varepsilon = 1/k$; the algorithm may depend on $k$.

## Sources

- C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and complexity classes", Journal of Computer and System Sciences 43 (1991), 425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Chapter 11.
