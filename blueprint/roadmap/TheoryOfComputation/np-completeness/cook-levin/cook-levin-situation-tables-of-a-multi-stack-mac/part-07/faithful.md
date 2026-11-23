# Faithful literal list

A list $\ell$ of literals $(p, b)$, each a variable index
$p \in \mathbb{N}$ with a sign $b$, is faithful for $V \in \mathbb{N}$ when every literal $(p, b)$
of $\ell$ has $p < V$ and the first literal of $\ell$ with index $p$ is $(p, b)$.

Equivalently, every literal of $\ell$ survives into the dense clause over $V$ variables built from
$\ell$: it is in range, and not shadowed by an earlier literal at the same index with the other
sign.
