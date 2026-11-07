# Fully polynomial-time approximation schemes

A maximization problem $P$ has an FPTAS
when $P$ is an NPO problem and there is one polynomial-time algorithm $A$ such that, for every
integer $k \ge 1$, every instance $x$ and every feasible solution $s$ for $x$, the output
$A(x, 1^k)$ of $A$ on $x$ with the unary precision tape of length $k$ is a feasible solution for
$x$ whose value is at least $1 - 1/k$ times the value of $s$.

Since the precision tape is unary, polynomial time in the total input length is polynomial
time in $|x|$ and $1/\varepsilon$, where $\varepsilon = 1/k$.

## Sources

- C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and complexity classes", Journal of Computer and System Sciences 43 (1991), 425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Chapter 11.
