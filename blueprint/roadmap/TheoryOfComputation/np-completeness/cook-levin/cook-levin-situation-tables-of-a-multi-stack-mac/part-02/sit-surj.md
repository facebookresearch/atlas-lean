# Situation surjectivity

Let $E$ be an encoding of a finite multi-stack Turing machine $M$
with $A_0$ label/state codes, $K$ stacks, $g$ symbol codes, window depth $d$ and $N$ situations.
For every $c < A_0$ and every $w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ with $w(k, j) < g$
for all $k < K$ and $j < d$, there is a situation $i < N$ whose label/state code
$\mathrm{la}(i)$ equals $c$ and whose window codes satisfy $\mathrm{wa}(i, k, j) = w(k, j)$ for
all $k < K$ and $j < d$.
