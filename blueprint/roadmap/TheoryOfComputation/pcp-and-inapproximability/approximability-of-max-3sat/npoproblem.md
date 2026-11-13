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

Feasible solutions on every instance are needed for completeness: an L-reduction to a problem
with no feasible solutions on some instance would have to map a feasible target output back to
a feasible source solution that does not exist.
