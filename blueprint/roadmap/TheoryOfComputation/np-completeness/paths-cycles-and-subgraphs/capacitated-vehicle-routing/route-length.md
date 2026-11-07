# Length of a route

Let $D$ be a list of lists of natural numbers, read as a distance
matrix whose entry $D_{u,v}$ is the entry at position $v$ of the row at position $u$ (positions
counted from $0$), or $0$ if there is no such entry, and let $o$ be a natural number, the depot.
The length of the empty route is $0$, and the length of a route given by a list
$(r_1, \dots, r_k)$ of natural numbers with $k \ge 1$ is
$D_{o,r_1} + \sum_{j=1}^{k-1} D_{r_j,r_{j+1}} + D_{r_k,o}$, where the sum is $0$ when $k = 1$.
