# NPO optimization problems

Let $P$ be an optimization problem whose instances $x$ and
solutions $s$ are bitstrings, with rational value $\mathrm{val}(x, s)$ and feasibility predicate
$\mathrm{feas}(x, s)$. Then $P$ is an NPO problem when the map $(x, s) \mapsto \mathrm{feas}(x, s)$
is polynomial-time computable, and there is a polynomial-time computable map $\mathrm{enc}$
sending each pair $(x, s)$ to a triple $(b, a, d)$ of a boolean and two natural numbers such
that, for all $x$ and $s$: $d \neq 0$; if $s$ is feasible for $x$, then
$\mathrm{val}(x, s) = \sigma a / d$, where $\sigma = -1$ if $b$ is true and $\sigma = 1$
otherwise; and if $s$ is not feasible for $x$, then $\mathrm{val}(x, s) = 0$.

The approximation classes APX, PTAS and FPTAS all require this condition. Without it, a problem
could hide an undecidable feasibility relation while assigning value $0$ everywhere, and the
constant empty-solution algorithm would vacuously satisfy the approximation guarantees.

## Sources

- C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and complexity classes", Journal of Computer and System Sciences 43 (1991), 425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Chapter 11.
