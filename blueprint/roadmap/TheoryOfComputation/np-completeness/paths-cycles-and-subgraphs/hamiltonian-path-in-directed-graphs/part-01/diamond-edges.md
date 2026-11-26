# Arcs of a variable diamond

Let $\varphi$ be a CNF formula with $m$ clauses, and write
$T(i)$ for the top of diamond $i$ and $R(i, l)$ for its row vertex $l$. The arcs of diamond $i$
for variable $x$ are $T(i) \to R(i, 0)$, $T(i) \to R(i, 3m)$, $R(i, 0) \to T(i + 1)$ and
$R(i, 3m) \to T(i + 1)$; for every $l < 3m$, both $R(i, l) \to R(i, l + 1)$ and
$R(i, l + 1) \to R(i, l)$; and for every clause $j < m$, the arcs $R(i, 3j + 1) \to j$ and
$j \to R(i, 3j + 2)$ if $x$ occurs positively in clause $j$, and the arcs $R(i, 3j + 2) \to j$
and $j \to R(i, 3j + 1)$ if $x$ occurs negatively in clause $j$. Here $j$ is the vertex of
clause $j$.
