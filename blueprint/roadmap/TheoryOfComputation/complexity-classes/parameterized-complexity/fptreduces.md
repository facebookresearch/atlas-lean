# FPT-reductions

A parameterized problem $P$ FPT-reduces to a parameterized problem $Q$
when there are a map $R$, sending each pair $(x, k)$ of a bitstring $x$ and a natural number
$k$ to such a pair $R(x, k) = (x', k')$, that is computable in FPT time, and a computable
function $g : \mathbb{N} \to \mathbb{N}$, such that for every bitstring $x$ and every
$k \in \mathbb{N}$, $k' \le g(k)$ and $P(x, k)$ is true if and only if $Q(x', k')$ is true.
