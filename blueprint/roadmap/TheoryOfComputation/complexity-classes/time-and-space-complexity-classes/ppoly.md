# Polynomial time with polynomial advice

The class P/poly consists of the decision problems
$L$ for which there are a polynomial $p$ with natural-number coefficients, bitstrings
$a_0, a_1, a_2, \ldots$ with $|a_n| \le p(n)$ for every $n$, and a polynomial-time computable
function $R$ on pairs of bitstrings such that for every bitstring $x$, $L(x)$ is true if and only
if $R(x, a_{|x|})$ is true.
