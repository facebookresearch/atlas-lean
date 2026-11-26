# 0-1 integer programming instances

A 0-1 integer programming instance is a triple
$(n, A, b)$ consisting of a natural number $n$ (the number of variables), a coefficient matrix
$A$ given as a list of rows, each row a list of pairs of natural numbers, and a right-hand side
$b$ given as a list of pairs of natural numbers. Each pair is any two naturals $(p, q)$
representing the integer $p - q$; the code is not canonical (both $(2, 1)$ and $(1, 0)$ represent
$1$), and no condition requires either component to be zero.
