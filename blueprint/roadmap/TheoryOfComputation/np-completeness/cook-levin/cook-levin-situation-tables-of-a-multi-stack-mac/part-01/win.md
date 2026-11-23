# Decoded windows of a situation

Let $E$ be an encoding of a finite multi-stack Turing
machine $M$ with window depth $d$, and let $i$ be a natural number. The window of situation $i$ on
stack $k$ is the list of length $d$ whose entry at position $j < d$ decodes the window symbol code
$c$ of situation $i$ on the stack number of $k$ at depth $j$. A code with $1 \le c \le s_k$, where
$s_k$ is the size of the effective alphabet of $k$, decodes to the effective symbol of $k$ with
index $c - 1$; every other code decodes to the empty cell $\bot$.
