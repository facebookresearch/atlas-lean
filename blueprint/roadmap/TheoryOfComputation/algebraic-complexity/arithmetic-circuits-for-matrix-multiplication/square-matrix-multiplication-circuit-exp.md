# Square matrix multiplication circuit exponent

For a field $F$, the square matrix
multiplication circuit exponent of $F$ is the rectangular circuit exponent of $F$ at aspect $1$.
Since $\lceil n^1 \rceil = n$, it is the infimum in $[0, \infty]$ of the reals $w \ge 0$ such that
for every $\varepsilon > 0$ there are $C > 0$ and $N \ge 1$ such that for every $n \ge N$ some
arithmetic circuit over $F$ of size at most $C n^{w + \varepsilon}$ computes the product of two
$n \times n$ matrices, and it is $\infty$ when there is no such $w$.
