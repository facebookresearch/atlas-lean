# Window symbol code of a situation

Let $E$ be an encoding of a finite multi-stack Turing
machine $M$, let $s_\kappa$ be the size of the effective alphabet of stack $\kappa$ in $E$, let
$g = 1 + \max_\kappa s_\kappa$ (so the empty-cell code $0$ and every effective symbol code are
below $g$), and let $d$ be the window depth of $M$. For natural numbers $i$, $k$ and $j$, the
window symbol code of situation $i$ on stack number $k$ at depth $j$ is the base-$g$ digit of $i$
at position $kd + j$, namely $\lfloor i / g^{kd + j} \rfloor \bmod g$.
