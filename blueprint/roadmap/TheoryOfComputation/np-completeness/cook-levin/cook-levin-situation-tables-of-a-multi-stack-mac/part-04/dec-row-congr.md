# C1e (the row decoder reads only the window)

Let $E$ be an encoding of a machine $M$
with $K$ numbered stacks, let $H, n \in \mathbb{N}$, and let
$w, w' : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$. If $w(k, j) = w'(k, j)$ for all $k < K$ and
$j < H$, then the row decoder of $E$ at height $H$ returns the same configuration on code $n$
and array $w$ as on code $n$ and array $w'$.
