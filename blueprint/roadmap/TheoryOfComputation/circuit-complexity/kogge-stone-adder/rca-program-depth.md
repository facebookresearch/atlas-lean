# Gate depths of the ripple-carry adder

For natural numbers $n$, $g \le 5n$ and $j < g$,
evaluating the first $g$ gates of the $n$-bit ripple-carry adder in $\mathbb{N}$, with every
input at depth $0$ and every gate one deeper than its deepest argument, gives gate $j$ the depth
$d(j)$. Here, with $q = \lfloor j / 5 \rfloor$, $c(0) = 0$ and $c(i) = 2i + 1$ for $i \ge 1$,
$d(j) = 1$ if $j \bmod 5 \in \{0, 2\}$, $d(j) = \max(1, c(q)) + 1$ if $j \bmod 5 \in \{1, 3\}$,
and $d(j) = c(q + 1)$ if $j \bmod 5 = 4$.
