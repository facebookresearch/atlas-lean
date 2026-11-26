# The counting class $\#P$

A function $f$ from bitstrings to natural numbers is in
$\#P$ when there are a polynomial $p$ with natural-number coefficients and a
polynomial-time computable Boolean function $R$ on pairs of bitstrings such that for every
bitstring $x$, $f(x)$ is the number of bitstrings $w$ of length exactly $p(|x|)$ for which
$R(x, w)$ is true.
