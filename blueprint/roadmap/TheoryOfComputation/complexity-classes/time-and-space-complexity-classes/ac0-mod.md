# The class $\mathsf{AC}^0(m)$

For a natural number $m$, a decision problem $L$ on
bitstrings is in $\mathsf{AC}^0[m]$ when there are a depth bound $d$, a polynomial $p$ with
natural-number coefficients and, for every $n$, a flat Boolean circuit $C_n$ on $n$ inputs such
that for every $n$: every gate of $C_n$ refers only to earlier gates; every mod gate of $C_n$ has
modulus $m$; $C_n$ has at most $p(n)$ gates and depth at most $d$; and for every bitstring $x$ of
length $n$, $L(x)$ is true if and only if $C_n$ has a last gate and the value of that gate on
input $x$ is true.

The and and or gates have unbounded fan-in, the family $(C_n)$ need not be uniform, and a circuit
with no mod gates also qualifies.
