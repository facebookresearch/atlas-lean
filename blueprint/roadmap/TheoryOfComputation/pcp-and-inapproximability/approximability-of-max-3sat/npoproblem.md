# NPO problems

An NPO (NP optimization) problem consists of a rational-valued value
function $v$, a Boolean feasibility predicate $F$ and an objective encoding $e$, each taking an
instance $x$ and a solution $s$ (both bitstrings), together with a polynomial $b$ with
natural-number coefficients, such that the following hold. $F$ and $e$ are polynomial-time
computable. For all $x$ and $s$, $e(x, s)$ is a triple $(\sigma, p, q)$ of a Boolean $\sigma$
and natural numbers $p$ and $q$ with $q \ne 0$; if $s$ is feasible for $x$ (that is,
$F(x, s)$ is true), then $v(x, s) = -p/q$ when $\sigma$ is true and $v(x, s) = p/q$ when
$\sigma$ is false, and otherwise $v(x, s) = 0$; and $v(x, s) \ge 0$. Every feasible solution
$s$ for $x$ has $|s| \le b(|x|)$, and every instance $x$ has a feasible solution.

Without feasible solutions on every instance, L-reductions would degenerate: an instance $x$ of
the source problem with no feasible solution could not be reduced to an instance $f(x)$ that has
one, since a feasible solution of $f(x)$ would have to be mapped back to a feasible solution of
$x$, while an instance $f(x)$ with no feasible solution would satisfy that requirement
vacuously.
