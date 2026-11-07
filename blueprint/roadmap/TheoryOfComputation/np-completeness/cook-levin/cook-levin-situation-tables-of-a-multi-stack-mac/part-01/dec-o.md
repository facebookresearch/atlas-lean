# Decoding a symbol code

For an encoding $E$ of a finite TM2 machine $M$, a stack $k$
and a natural number $c$, the decoded symbol is the effective symbol of stack $k$ with index
$c - 1$ when $1 \le c$ and $c - 1 < s_k$, where $s_k$ is the size of the effective alphabet of
stack $k$; otherwise, in particular for $c = 0$, it is $\bot$ (no symbol).
