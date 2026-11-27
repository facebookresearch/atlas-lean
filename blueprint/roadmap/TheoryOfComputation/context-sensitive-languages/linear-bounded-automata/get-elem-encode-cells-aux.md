# Entries of the cell-tuple encoding

Let $Q$ and $\Gamma$ be sets, let $w = w_0 \cdots w_{n-1}$ be a word over $\Gamma$ and $x = x_0 \cdots
x_{n-1}$ a list of tape cells (letters of $\Gamma$ or blanks) of the same length $n$, let $h$ be a natural
number or undefined, let $q \in Q$, let $t, N$ be natural numbers and let $i < n$. The $i$-th entry of the
cell-tuple encoding of $(w, x, h, q, t, N)$ is $(w_i, x_i, s, 1, \beta(t + i, N))$, where $s = q$ if
$h = i$ and $s = \bot$ otherwise, and $\beta(h, n)$ denotes the boundary tag of position $h$ on a tape of length $n$ (both if $h = 0$ and $n = 1$; left if $h = 0$ and $n \ne 1$; right if $h \ne 0$ and $h + 1 = n$; middle otherwise).
