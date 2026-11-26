# 3-colorability by witness bits

Let $n \in \mathbb{N}$ and let $es$ be a list of pairs of
natural numbers whose entries are all less than $n$. The graph on the vertices $0, \dots, n-1$
with edge list $es$ (symmetrized, loops dropped) is 3-colorable iff there is a list $w$ of exactly
$2n$ bits such that, writing the color code of vertex $i$ for the pair of bits $2i$ and $2i+1$ of
$w$, the color code of every vertex $i < n$ is valid (not $11$), and for every edge $(u, v)$ in
$es$ with $u \ne v$ the color codes of $u$ and $v$ differ.
