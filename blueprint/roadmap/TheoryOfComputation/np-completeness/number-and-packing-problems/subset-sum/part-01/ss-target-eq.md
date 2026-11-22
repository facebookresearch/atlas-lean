# The target in base 4

Let $k, n \in \mathbb{N}$, let $b$ be a list of booleans, and let $m$
be the length of the list of vertex pairs $(i, j)$, $i < j < n$. The reduction's target for $k$,
$n$ and $b$ equals $k \cdot 4^m + \sum_{q < m} c_q 4^q$, where $c_q = 2$ if entry $q$ of $b$
(counting from $0$) is true and $c_q = 0$ otherwise, in particular when $b$ has no entry $q$.
