# Myhill's isomorphism theorem, hard direction

The following holds. Let $A, B \subseteq \mathbb{N}$ be 1-equivalent: there are computable injective functions $f, g : \mathbb{N} \to \mathbb{N}$ with $n \in A \iff f(n) \in B$ and $n \in B \iff g(n) \in A$ for all $n$. Then $A$ and $B$ are recursively isomorphic: there is a computable bijection $h : \mathbb{N} \to \mathbb{N}$ with

$$n \in A \iff h(n) \in B \quad \text{for all } n \in \mathbb{N}.$$

No recursive enumerability of $A$ or $B$ is assumed.

## Sources

- R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Ch. I §5, p. 24 (Myhill's isomorphism theorem).
- H. Rogers, *Theory of Recursive Functions and Effective Computability*, §7.6.
