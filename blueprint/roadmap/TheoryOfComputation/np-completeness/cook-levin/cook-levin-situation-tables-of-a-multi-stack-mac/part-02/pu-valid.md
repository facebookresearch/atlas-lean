# Pushed codes are valid symbol codes

Fix an encoding record $E$ of a finite multi-stack
machine. Let $i$ be a situation, $k$ a stack number, $s$ the stack that the inverse stack numbering
of $E$ assigns to $k$, $n_s$ the size of the effective alphabet of $s$, and $j < \mathrm{pl}(i, k)$.
Then there is a symbol $x$ at position $j$ from the top (counting from $0$) among the symbols the
effect of situation $i$ leaves pushed on $s$, such that $\mathrm{pu}(i, k, j)$ is the code of $x$,
$1 \le \mathrm{pu}(i, k, j) \le n_s$, and decoding $\mathrm{pu}(i, k, j)$ on stack $s$ gives $x$.
