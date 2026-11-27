# Matrix multiplication tensor contraction

Let $F$ be a field, let $m, n, p$ be natural
numbers, let $A \in F^{m \times n}$ and $B \in F^{n \times p}$, and let $i < m$ and $k < p$. Write
$T$ for the matrix multiplication tensor over $F$ for $m, n, p$ and, for a natural number $q$,
$[q] = \{0, \dots, q - 1\}$. The contraction of $T$ against $A$ and $B$ at output coordinate
$(i, k)$ is

$$\sum_{a \in [m] \times [n]} \sum_{b \in [n] \times [p]} T(a, b, (k, i)) \, A_a \, B_b,$$

where $A_a$ and $B_b$ are the entries of $A$ and $B$ at the matrix coordinates $a$ and $b$.
