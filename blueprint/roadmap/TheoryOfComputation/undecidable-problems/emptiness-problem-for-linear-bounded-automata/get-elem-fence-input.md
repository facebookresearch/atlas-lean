# Cells of a fenced input

Let $w$ be a word of length $\ell$ and $i, j, n \in \mathbb{N}$.
The cell at position $n$, counting from $0$, of the fenced input of $w$ with $i$ left and $j$
right padding cells is the wall if $n = 0$; a left padding cell if $1 \le n \le i$; the letter of
$w$ at position $n - i - 1$, also counting from $0$, as a symbol, if $i < n \le i + \ell$; a right
padding cell if $i + \ell < n \le i + \ell + j$; the wall if $n = i + \ell + j + 1$; and there is
no cell at a larger position $n$.
