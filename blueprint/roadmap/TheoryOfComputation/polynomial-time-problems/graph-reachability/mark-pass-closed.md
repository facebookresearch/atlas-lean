# A pass marks the heads of arcs with marked tails

Let $n \in \mathbb{N}$, let $E$ be a
list of pairs of natural numbers and let $m$ be a list of booleans, where $m$ marks $w$ when
$w < |m|$ and the $w$-th entry of $m$ (counting from $0$) is true. If $(u, v) \in E$ with $u < n$
and $v < n$, $v < |m|$ and $m$ marks $u$, then the result of the marking pass of $E$ with bound $n$
on $m$ marks $v$.
