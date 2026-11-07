# Polyline closure of a braid word

Let $n \in \mathbb{N}$, and let
$w = w_0 w_1 \cdots w_{m-1}$ be a braid word (a list of integers, where $i > 0$ stands for
$\sigma_i$ and $-i$ for $\sigma_i^{-1}$). If $m = 0$, the value is the junk list $(0, 0, 0)$,
$(1, 0, 0)$, $(0, 1, 0)$. Otherwise the value is a list of vertices in $\mathbb{R}^3$ tracing the
closure of $w$ as one polyline component. It starts at the vertex $(1, 0, 0)$ on strand position
$1$ and makes passes through the braid: in each pass the crossing $w_j$ occupies the slab between
heights $z = -(j + 1)$ and $z = -j$, with the strand passing over lifted to $y = 1$, and each
pass is followed by a closure arc through $y = 100$ back up to height $z = 0$. Tracing stops as
soon as a pass ends at position $1$, or after $n$ passes.

The layout is designed for words with $1 \le |w_j| \le n - 1$ for every $j$, where the strands
sit at the $x$-positions $1, \dots, n$; other words still yield a vertex list, but not a
meaningful one.
