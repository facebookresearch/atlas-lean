# Matrix multiplication tensor

For a field $F$ and natural numbers $m$, $n$, $p$, the matrix
multiplication tensor is the array over $F$ indexed by triples $((i, j), (j', k), (k', i'))$ of an
$m \times n$, an $n \times p$ and a $p \times m$ matrix coordinate, whose entry is $1$ if $j = j'$,
$k = k'$ and $i' = i$, and $0$ otherwise.

These are the coefficients of $\sum_{i, j, k} e_{(i,j)} \otimes e_{(j,k)} \otimes e_{(k,i)}$, the
tensor of multiplying an $m \times n$ matrix by an $n \times p$ matrix.
