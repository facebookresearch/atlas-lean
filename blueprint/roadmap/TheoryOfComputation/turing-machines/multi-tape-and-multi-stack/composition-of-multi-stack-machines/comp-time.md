# Time bound of the composite machine

Let $p_1, p_2 \in \mathbb{N}[X]$ be the polynomial time
bounds of a machine $M_1$ computing $f$ and a machine $M_2$ computing $g$, and let $c$ be the sum,
over the labels of $M_1$, of the number of push instructions in the statement at that label. The
composite time bound is the polynomial $p_1 + 4(X + c\,p_1) + 2 + p_2 \circ (X + c\,p_1)$.

The two copy loops take $2m + 1$ steps each on an intermediate string of length
$m \le n + c\,p_1(n)$, where $n$ is the input length.
