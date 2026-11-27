# Points from a scoring vector

Under a positional scoring vector $\alpha = (\alpha_1, \alpha_2, \dots)$, a voter with ranking $v$ gives candidate $c$ the points $\alpha_j$ when $c$ is at position $j$ of $v$; a candidate missing from $v$ is treated as being at position $|v| + 1$, so it gets $\alpha_{|v|+1}$ (or $0$ if $\alpha$ has fewer than $|v| + 1$ entries), and a position beyond $\alpha$ gives $0$ points.
