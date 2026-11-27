# Cell tuples of an LBA configuration from an offset

Let $Q$ and $\Gamma$ be sets. Let $w = w_0 \cdots w_{n-1}$ be a word over $\Gamma$, let $x_0 \cdots
x_{k-1}$ be a list of tape cells (letters of $\Gamma$ or blanks), let $h$ be a natural number or
undefined (the head position), let $q \in Q$, and let $t, N$ be natural numbers (the offset of the first
cell and the total length). The cell-tuple encoding of $(w, x, h, q, t, N)$ is the list of $m = \min(n,
k)$ cell tuples whose $j$-th entry, for $j < m$, is $(w_j, x_j, s_j, 1, \beta(t + j, N))$, where $s_j =
q$ if $h = j$ and $s_j = \bot$ otherwise (in particular every $s_j = \bot$ if $h$ is undefined), and
$\beta(h, n)$ denotes the boundary tag of position $h$ on a tape of length $n$ (both if $h = 0$ and $n = 1$; left if $h = 0$ and $n \ne 1$; right if $h \ne 0$ and $h + 1 = n$; middle otherwise).
