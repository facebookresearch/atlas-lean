# Rank-two exchange recurrence

For natural numbers $b, c$ and elements $x, y$ of a field $K$, the rank-two exchange recurrence
is the sequence $(z_k)_{k \ge 0}$ in $K$ with $z_0 = x$, $z_1 = y$ and

$$z_{k+2} = \frac{z_{k+1}^{e_k} + 1}{z_k}, \qquad e_k = c \text{ for even } k, \quad e_k = b \text{ for odd } k,$$

where a quotient by $0$ is read as $0$. When $b$ and $c$ are both positive, or both zero, so that
$\begin{pmatrix} 0 & b \\ -c & 0 \end{pmatrix}$ is an exchange matrix, the shift $z_k = z'_{k+1}$
turns this into the exchange relation $z'_{m-1} z'_{m+1} = (z'_m)^c + 1$ for even $m$ and
$z'_{m-1} z'_{m+1} = (z'_m)^b + 1$ for odd $m$ of the coefficient-free cluster algebra
$\mathcal{A}(b, c)$ with initial cluster $(z'_1, z'_2) = (x, y)$, as long as the terms are nonzero.

## Sources

- S. Fomin, L. Williams and A. Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5, Section 3.2, equation (3.2.2).
