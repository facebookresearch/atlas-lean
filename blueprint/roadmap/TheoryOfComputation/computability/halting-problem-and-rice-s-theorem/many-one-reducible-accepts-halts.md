# Acceptance reduces to halting

Say a partial recursive code $c$ accepts a natural number
$n$ when $c$ halts on input $n$ with output $0$. Acceptance many-one reduces to halting: there is
a computable map $f$ from pairs $(c, n)$ of a partial recursive code and a natural number to such
pairs, such that for every pair $(c, n)$, the code $c$ accepts $n$ if and only if, writing
$f(c, n) = (c', n')$, the code $c'$ halts on $n'$.

The reduction runs the code, then loops unless the output is $0$.
