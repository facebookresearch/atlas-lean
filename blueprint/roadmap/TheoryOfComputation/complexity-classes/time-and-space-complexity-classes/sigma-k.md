# The class $\Sigma_k^p$

For a natural number $k$, a decision problem $L$ is in
$\Sigma_k^p$ when there are a polynomial $p$ with natural-number coefficients and a
polynomial-time computable Boolean function $R$ of a bitstring and a list of bitstrings such
that for every bitstring $x$, $L(x)$ is true if and only if
$Q_1 w_1\, Q_2 w_2 \cdots Q_k w_k$ with $R(x, [w_1, \dots, w_k])$ true, where $Q_i$ is $\exists$
for odd $i$ and $\forall$ for even $i$, and each $w_i$ ranges over bitstrings of length at
most $p(|x|)$. For $k = 0$ the condition is that $R(x, [\,])$ is true.
