# The arithmetical hierarchy is strict

The classes $\Sigma_n$ and $\Pi_n$ of subsets of $\mathbb{N}$ are defined by: $\Sigma_0$ consists of the computable sets; a set $A$ is in $\Sigma_{n+1}$ if there is a $B \in \Pi_n$ with

$$x \in A \iff \exists y\; \langle x, y \rangle \in B \quad \text{for all } x \in \mathbb{N},$$

where $\langle \cdot, \cdot \rangle$ is a pairing bijection $\mathbb{N}^2 \to \mathbb{N}$; and $\Pi_n$ is defined dually, starting with a universal quantifier.

The following holds: for every $n \in \mathbb{N}$ there is a set $A \subseteq \mathbb{N}$ with $A \in \Sigma_{n+1}$ and $A \notin \Sigma_n$.

## Sources

- R. I. Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 4.6.
- H. Rogers, *Theory of Recursive Functions and Effective Computability*, §13.5.
