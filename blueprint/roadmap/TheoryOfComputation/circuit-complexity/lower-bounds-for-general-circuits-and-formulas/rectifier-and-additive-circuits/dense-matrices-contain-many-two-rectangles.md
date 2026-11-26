# Dense Boolean matrices contain many 2-rectangles, and the 2-rectangle lift

Let $A$ be an $m\times m$ Boolean matrix with $4m^3\le|A|^2$ (that is, $|A|\ge 2m^{3/2}$). Then the number of $2\times2$ all-ones submatrices of $A$ is at least $|A|^4/(32m^4)$. Moreover, let $B$ be the $\binom m2\times\binom m2$ *$2$-rectangle lift* of $A$, whose entry at (pair of rows, pair of columns) is $1$ iff those rows and columns span an all-ones $2\times2$ submatrix of $A$. If $A$ is $k$-free then $B$ is $(\binom{k-1}{2}+1)$-free.

## Proof sketch

Count pairs of ones in common columns by convexity (Cauchy–Schwarz) twice. For the lift, an all-ones $t\times t$ submatrix of $B$ with $t=\binom{k-1}2+1$ involves more than $\binom{k-1}2$ row pairs, hence at least $k$ rows of $A$, and similarly $k$ columns, which span an all-ones $k\times k$ submatrix of $A$.

## Depends on

- [k-free (rectangle-free) Boolean matrices](k-free-boolean-matrices.md)

## Sources

- Igor S. Sergeev, "On Relative OR-Complexity of Boolean Matrices and Their Complements", 2014.
