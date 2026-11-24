# Well-formed rows of cells

Let $M$ be a finite multi-stack Turing machine and $E$ an
encoding of $M$ with $K$ numbered stacks, let $H \in \mathbb{N}$, and let
$w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ assign a code $w(k, j)$ to each stack number $k$
and depth $j$. The row $w$ is well formed at height $H$ when for every $k < K$ and every $j < H$:
$w(k, j)$ is at most the size of the effective alphabet of the stack numbered $k$, and if
$w(k, j) = 0$ then $w(k, b) = 0$ for every $b$ with $j \le b < H$.

Code $0$ is the empty cell, so the second condition says that each stack is in prefix form.
