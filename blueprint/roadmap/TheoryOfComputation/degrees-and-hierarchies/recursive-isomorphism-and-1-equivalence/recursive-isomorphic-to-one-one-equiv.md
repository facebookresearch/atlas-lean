# A recursive isomorphism gives a 1-equivalence

Let $P$ and $Q$ be predicates on
$\mathbb{N}$. If $P$ and $Q$ are recursively isomorphic, then they are 1-equivalent: $P$ is
one-one reducible to $Q$ and $Q$ is one-one reducible to $P$. Here $P$ is one-one reducible to
$Q$ when there is a computable injective function $g : \mathbb{N} \to \mathbb{N}$ such that for
every $n$, $P(n)$ holds if and only if $Q(g(n))$ holds.

This is the easy direction of Myhill's isomorphism theorem.

## Sources

- Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 7.1.
