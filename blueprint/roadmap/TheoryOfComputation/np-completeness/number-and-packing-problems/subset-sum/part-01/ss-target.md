# Target of the SUBSET-SUM reduction

Let $m = n(n-1)/2$ be the number of vertex pairs
$(i, j)$ with $i < j < n$, and let $b$ be a list of pair bits. For $k \in \mathbb{N}$ the target
is $k \cdot 4^m + \sum 2 \cdot 4^q$, the sum over the indices $q < m$ such that bit $b_q$ is set
(an index past the end of $b$ counts as unset). So the quotient of the target by $4^m$ is $k$, and
its base-$4$ digit at position $q < m$ is $2$ when $b_q$ is set and $0$ otherwise.
