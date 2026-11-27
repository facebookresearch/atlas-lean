# Correctness of the reduction

Let $V$ be a polynomial-time Turing machine that computes a
Boolean function $f$ on pairs of bit strings, reading a pair $(a, y)$ as the bits of $a$, a
separator, then the bits of $y$, and writing its answer as one bit. Let $p$ be a polynomial with
natural-number coefficients, $R$ a relation on bit strings with $R(a, y)$ iff $f(a, y)$ is true,
and $L'$ a predicate on bit strings such that $L'(a)$ holds iff some bit string $y$ of length at
most $p(|a|)$ satisfies $R(a, y)$. Then for every bit string $a$, $L'(a)$ holds iff the image of
$a$ under the reduction built from $V$ and $p$ is in CNF-SAT.
