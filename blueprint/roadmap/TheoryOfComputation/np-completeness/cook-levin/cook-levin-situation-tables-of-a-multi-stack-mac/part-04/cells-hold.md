# Cell literals of an array hold in a row

Let $E$ be an encoding of a machine $M$ with
$K$ numbered stacks, let $a$ be a list of booleans, let $H, t \in \mathbb{N}$, and let
$w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$. The cell literals of $w$ hold in row $t$ under
$a$ when, for all $k < K$ and $j < H$, the cell variable for time $t$, stack $k$, depth $j$ and
symbol code $w(k, j)$ in the layout of $E$ at height $H$ is true under $a$, that is, its index is
less than the length of $a$ and the entry of $a$ at that index is true.

Unlike the exact form, this says nothing about the cell variables for other symbol codes.
