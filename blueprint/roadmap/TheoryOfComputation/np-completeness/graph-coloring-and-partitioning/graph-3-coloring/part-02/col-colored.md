# Colorings that follow an assignment

Let $s$ be a construction state, let
$v : \mathbb{N} \to \mathrm{Bool}$ be an assignment, and let $c : \mathbb{N} \to \{0, 1, 2\}$ be a
coloring. Then $c$ colors $s$ according to $v$ when $c(0) = 0$, $c(1) = 1$ and $c(2) = 2$ (the
palette vertices $T$, $F$, $B$), $c(a) \ne c(b)$ for every edge $(a, b)$ emitted in $s$, and for
every occurrence recorded in $s$ with variable $x$, polarity $b$, literal vertex $L$ and negation
vertex $M$: if $v(x) = b$ then $c(L) = 0$ and $c(M) = 1$, and otherwise $c(L) = 1$ and
$c(M) = 0$.
