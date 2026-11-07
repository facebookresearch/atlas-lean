# Optimization problems

An optimization problem consists of a function $v$ assigning a
rational value $v(x, s)$ to every instance $x$ and every candidate solution $s$, both bitstrings;
a feasibility predicate saying whether $s$ is a feasible solution for $x$; and a polynomial $p$
with natural-number coefficients such that every feasible solution $s$ for $x$ has length at
most $p(|x|)$. It is required that $v(x, s) \ge 0$ for all $x$ and $s$, that $v(x, s) = 0$
whenever $s$ is not feasible for $x$, and that every instance has a feasible solution.

The problem is read as a maximization problem. The structure carries no computational content:
polynomial-time feasibility and a polynomial-time encoding of the objective form a separate
predicate (NPO), which the approximation classes APX, PTAS and FPTAS require.

## Sources

- C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and complexity classes", Journal of Computer and System Sciences 43 (1991), 425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Chapter 11.
