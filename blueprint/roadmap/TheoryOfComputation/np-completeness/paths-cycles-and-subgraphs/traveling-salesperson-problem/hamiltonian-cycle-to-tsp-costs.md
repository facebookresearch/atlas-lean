# Costs produced by the Hamiltonian-cycle to TSP converter

Let $G$ be a simple graph on the
vertex set $\{0, \dots, n-1\}$, let $x$ be a Boolean array of length $n^2$ such that for all
$i, j < n$ the cell of $x$ at index $in + j$ exists and is true exactly when $i$ and $j$ are
adjacent in $G$, and let $y$ be the array output by the Hamiltonian-cycle to TSP converter on $x$,
with a Boolean cell read as $1$ if true and $0$ if false. Then for all $i, j < n$ the cell of $y$
at index $in + j$ exists and equals $0$ if $i$ and $j$ are adjacent in $G$ and $1$ otherwise; for
every $i < n$ the cell of $y$ at index $in + i$ exists and equals $1$; and for all $i, j < n$ the
cells of $y$ at indices $in + j$ and $jn + i$ are equal.
