# Σ₁ is the class of recursively enumerable predicates

A predicate $P$ on $\mathbb{N}$ is
recursively enumerable if and only if it is in $\Sigma_1$, that is, if and only if there is a
computable predicate $Q$ on $\mathbb{N}$ such that for all $x$, $P(x)$ holds iff
$Q(\langle x, y \rangle)$ holds for some $y$, where $\langle x, y \rangle$ is the standard pairing
function of $\mathbb{N}$.

This is the first level of Post's theorem.

## Sources

- Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 4.4 (Post).
