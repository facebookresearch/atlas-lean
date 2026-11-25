# Cell block of a row equal to an array

Let $E$ be an encoding of a machine $M$ with $K$
numbered stacks and $g$ symbol codes, let $a$ be a list of booleans, let $H, t \in \mathbb{N}$,
and let $w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$. The cell block of row $t$ is exactly
$w$ under $a$ when, for all $k < K$, $j < H$ and $x < g$, the cell variable for time $t$,
stack $k$, depth $j$ and symbol code $x$ in the layout of $E$ at height $H$ is true under $a$ if
and only if $x = w(k, j)$. A variable $v$ is true under $a$ when $v$ is less than the length of
$a$ and the entry of $a$ at position $v$ is true.
