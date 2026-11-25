# The universal levels of the polynomial hierarchy

For a natural number $k$, the class
$\Pi_k^p$ consists of the decision problems $L$ for which there are a polynomial $p$ with
natural-number coefficients and a polynomial-time computable function $R$, taking a bitstring and
a list of bitstrings to a boolean, such that for every bitstring $x$, $L(x)$ is true if and only
if

$$
\forall w_1\, \exists w_2\, \forall w_3 \cdots Q_k w_k\; R(x, [w_1, \ldots, w_k]) = \mathrm{true},
$$

where the $k$ quantifiers alternate starting with $\forall$ (so $Q_k$ is $\forall$ for odd $k$
and $\exists$ for even $k$) and each $w_i$ ranges over the bitstrings of length at most
$p(|x|)$. For $k = 0$ the condition is $R(x, []) = \mathrm{true}$.
