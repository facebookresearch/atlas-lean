# Every Σₙ predicate is Πₙ₊₁

Let $\Sigma_n$ and $\Pi_n$ be the levels of the arithmetical
hierarchy of predicates on $\mathbb{N}$: $\Sigma_0 = \Pi_0$ is the class of computable predicates,
$P \in \Sigma_{n+1}$ when for some $Q \in \Pi_n$ and all $x$, $P(x)$ holds iff
$Q(\langle x, y \rangle)$ holds for some $y$, and $P \in \Pi_{n+1}$ when for some $Q \in \Sigma_n$
and all $x$, $P(x)$ holds iff $Q(\langle x, y \rangle)$ holds for all $y$; here
$\langle x, y \rangle$ is the standard pairing function of $\mathbb{N}$. Then for every $n$, every
predicate in $\Sigma_n$ is in $\Pi_{n+1}$.

The proof adds a dummy universal quantifier.

## Sources

- Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 4.3.
