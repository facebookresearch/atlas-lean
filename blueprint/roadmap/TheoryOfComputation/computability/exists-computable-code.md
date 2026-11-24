# Parametrized s-m-n theorem

Let $\alpha$ be a type with a primitive recursive encoding into
the natural numbers, and for each $a \in \alpha$ let $F_a$ be a partial function from
$\mathbb{N}$ to $\mathbb{N}$, such that $(a, x) \mapsto F_a(x)$ is partial recursive. Then there
is a computable map $g$ from $\alpha$ to codes of partial recursive functions such that for all
$a \in \alpha$ and $x \in \mathbb{N}$, the partial function with code $g(a)$ agrees with $F_a$ at
$x$: both are undefined, or both are defined with the same value.
