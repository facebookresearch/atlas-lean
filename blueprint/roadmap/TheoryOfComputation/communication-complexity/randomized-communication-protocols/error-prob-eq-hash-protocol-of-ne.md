# Error of the random-hash protocol for equality

$\mathrm{EQ}_n : \{0,1\}^n \times \{0,1\}^n \to \{0, 1\}$ is the equality function ($1$ exactly when $x = y$). Here protocols have inputs $X = Y = \{0,1\}^n$. A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. A public-coin protocol with a finite set $R$ of random strings is a family $(p_r)_{r \in R}$ of protocols; its cost is the maximum of the depths of the $p_r$ ($0$ if $R$ is empty). For nonempty $R$, its error probability for $f : X \times Y \to \{0, 1\}$ at $(x, y)$ is the fraction $|\{r \in R : p_r \text{ outputs a value other than } f(x, y) \text{ on } (x, y)\}| / |R|$. The random-hash protocol for $\mathrm{EQ}_n$ with parameter $k$ is the public-coin protocol whose random strings are all maps $h : \{0,1\}^n \to \{0,1\}^k$: given $h$, Alice announces the $k$ bits of $h(x)$ one at a time, then Bob announces $1$ if the message equals $h(y)$ and $0$ otherwise, and the leaf outputs Bob's bit. For all $n, k \in \mathbb{N}$ and all $x, y \in \{0,1\}^n$ with $x \ne y$, the error
probability of the random-hash protocol with parameter $k$ for $\mathrm{EQ}_n$ at $(x, y)$ is exactly $1/2^k$:
it errs exactly when $h(x) = h(y)$.

## Background

- [Deterministic communication complexity of equality](../deterministic-communication-protocols/comm-complexity-eq-fn.md): every deterministic protocol for equality of $n \ge 1$ bits needs $n + 1$ bits.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Chapter 3: "if $x \ne y$, the probability that $h(x) = h(y)$ is at most $2^{-k}$".
