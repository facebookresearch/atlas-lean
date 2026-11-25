# Pair bits computed by a function

Let $n$ be a natural number, let $f$ be a function from
pairs of natural numbers to bits, and let $b$ be the list obtained by applying $f$ to each entry of
the pair list of $n$ (the pairs $(i, j)$ with $i < j < n$ in encoding order). Then for all
$i < j < n$, the bit of the pair $(i, j)$ in $b$ is $f(i, j)$.
