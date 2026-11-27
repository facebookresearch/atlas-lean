# A subset sum of the reduction's numbers in base 4

Let $n \in \mathbb{N}$, let $b$ be a
list of booleans, let $m$ be the length of the list of vertex pairs $(i, j)$, $i < j < n$, and let
$S$ and $F$ be finite sets of natural numbers with every element of $F$ below $m$. Write $x_v$ for
the vertex number of $v$ and $y_q$ for the pair number of $q$ defined from $n$ and $b$. For $q < m$
let $t_{v,q} = 1$ if entry $q$ of $b$ (counting from $0$) is true and $v$ is an endpoint of the
$q$-th pair, and $t_{v,q} = 0$ otherwise; let $f_q = 1$ if $q \in F$ and entry $q$ of $b$ is true,
and $f_q = 0$ otherwise. An absent entry counts as false. Then
$\sum_{v \in S} x_v + \sum_{q \in F} y_q = |S| \cdot 4^m +
\sum_{q < m} \left(\sum_{v \in S} t_{v,q} + f_q\right) 4^q$.
