# The arithmetical class $\Sigma_n$

A predicate $P$ on $\mathbb{N}$ is in $\Sigma_0$ when it is computable. It is in $\Sigma_{n+1}$
when there is a predicate $Q$ in $\Pi_n$ such that for every $x$, $P(x)$ holds if and only if
$Q(\langle x, y \rangle)$ holds for some $y$, where $\langle x, y \rangle$ is the pairing bijection $\mathbb{N}^2 \to \mathbb{N}$ given by $\langle x, y \rangle = y^2 + x$ if $x < y$ and $\langle x, y \rangle = x^2 + x + y$ otherwise. So a set in $\Sigma_n$ is defined by
$n$ alternating quantifiers over a computable relation, starting with an existential quantifier.

## Sources

- Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 4.1.
