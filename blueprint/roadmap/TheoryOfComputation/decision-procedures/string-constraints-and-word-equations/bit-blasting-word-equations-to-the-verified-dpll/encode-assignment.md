# Encoding a substitution as a SAT assignment

Let $n \in \mathbb{N}$ and let $\sigma$ assign a binary word $\sigma(x_i)$ to each $i < n$. The encoded
assignment $\nu_\sigma : \mathbb{N} \to \{0, 1\}$ is defined by $\nu_\sigma(0) = 1$ and, for $x \ge 1$, by
writing $x - 1 = \langle i, p\rangle$: $\nu_\sigma(x)$ is the $p$-th letter of $\sigma(x_i)$ if $i < n$ and
$p < |\sigma(x_i)|$, and $0$ otherwise. Here $\langle i, p\rangle$ denotes the pairing bijection $\mathbb{N}^2 \to \mathbb{N}$ given by $\langle i, p\rangle = p^2 + i$ if $i < p$ and $\langle i, p\rangle = i^2 + i + p$ otherwise.
