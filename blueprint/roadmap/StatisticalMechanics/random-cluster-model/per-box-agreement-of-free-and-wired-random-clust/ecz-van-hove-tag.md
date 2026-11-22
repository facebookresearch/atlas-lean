# Tiling cell of a box vertex

Let $d, m, n \in \mathbb{N}$ and $T = \lfloor (2n+1)/(2m+1) \rfloor$ is the [number of cells per side](ecz-t.md). For a vertex $x$ of $\Lambda_n = \{-n, \dots, n\}^d$ let $c_i = \lfloor \max(x_i + n, 0)/(2m+1) \rfloor$ be its [cell indices](ecz-cell-idx.md). If $c_i < T$ for every coordinate $i$, the tag of $x$ is $c = (c_i)_i \in \{0, \dots, T-1\}^d$; otherwise $x$ has no tag.
