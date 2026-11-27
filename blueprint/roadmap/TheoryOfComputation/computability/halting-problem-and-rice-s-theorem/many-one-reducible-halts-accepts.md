# Halting reduces to acceptance

Say a partial recursive code $c$ accepts a natural number
$n$ when $c$ halts on input $n$ with output $0$. Halting many-one reduces to acceptance: there is
a computable map $f$ from pairs $(c, n)$ of a partial recursive code and a natural number to such
pairs, such that for every pair $(c, n)$, the code $c$ halts on $n$ if and only if, writing
$f(c, n) = (c', n')$, the code $c'$ accepts $n'$.

The reduction runs the code, then outputs $0$.
