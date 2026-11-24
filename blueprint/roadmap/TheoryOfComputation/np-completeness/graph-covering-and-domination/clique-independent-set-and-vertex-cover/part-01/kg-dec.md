# Language of graph instances with a property

Let $P$ be a property of a natural number
$n$, a natural number $k$ and a simple graph on $\{0, \dots, n-1\}$. The decision problem accepts
a bit string $x$ exactly when, writing $1$ for true and $0$ for false, $x = 1^k\,0\,1^n\,0\,b$
for some natural numbers $k$, $n$ and a list of bits $b$ with one entry for each pair
$i < j < n$, such that $P$ holds of $n$, $k$ and the graph on $\{0, \dots, n-1\}$ given by $b$.
In that graph, distinct $i$ and $j$ are adjacent when the bit of the pair $\{i, j\}$ is true,
the pairs being listed with $i$ ascending and, for each $i$, $j$ descending.
