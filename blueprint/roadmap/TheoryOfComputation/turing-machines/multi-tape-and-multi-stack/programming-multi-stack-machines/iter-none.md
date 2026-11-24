# A halted run stays halted

Let $f$ be a partial function from a set $\sigma$ to itself (a step function, where being
undefined means halting), and let $\hat f$ be its extension to $\sigma$ with an added failure value
$\bot$: $\hat f(\bot) = \bot$, and for $x \in \sigma$, $\hat f(x) = f(x)$ if $f$ is defined at $x$
and $\hat f(x) = \bot$ otherwise. Then $\hat f^{\,n}(\bot) = \bot$ for every $n \in \mathbb{N}$.
