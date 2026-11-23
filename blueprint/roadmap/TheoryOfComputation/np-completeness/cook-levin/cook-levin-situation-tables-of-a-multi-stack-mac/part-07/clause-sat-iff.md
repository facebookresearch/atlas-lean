# Exact clause semantics

Let $V \in \mathbb{N}$, let $\ell$ be a list of pairs $(p, b)$ of a
variable index $p$ and a sign $b$ that is faithful for $V$, and let $a$ be a list of Booleans.
Then $a$ satisfies the dense clause over $V$ variables built from $\ell$ if and only if some
$(p, b) \in \ell$ has $p < |a|$ and $a_p = b$.
