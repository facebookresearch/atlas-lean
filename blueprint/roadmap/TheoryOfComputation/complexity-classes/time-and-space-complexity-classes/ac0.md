# The class $\mathsf{AC}^0$

A decision problem $L$ on bitstrings is in $\mathsf{AC}^0$ when
there are a depth bound $d$, a polynomial $p$ with natural-number coefficients and, for every
$n$, a flat Boolean circuit $C_n$ on $n$ inputs such that for every $n$: every gate of $C_n$
refers only to earlier gates; $C_n$ has no mod gates; $C_n$ has at most $p(n)$ gates and depth at
most $d$; and for every bitstring $x$ of length $n$, $L(x)$ is true if and only if $C_n$ has a
last gate and the value of that gate on input $x$ is true.

The and and or gates have unbounded fan-in, and the family $(C_n)$ need not be uniform.
