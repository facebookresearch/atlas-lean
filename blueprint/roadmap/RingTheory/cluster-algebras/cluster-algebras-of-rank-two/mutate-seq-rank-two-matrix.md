# Seed mutation in rank two is the rank-two recurrence

Let $(z_k)$ be the rank-two exchange recurrence for $b, c$ with $z_0 = x$ and $z_1 = y$. Starting
from the seed with cluster $(x, y)$ and exchange matrix
$\begin{pmatrix} 0 & b \\ -c & 0 \end{pmatrix}$ and mutating alternately in the first and the second
direction, $m$ times each, gives the seed with cluster $(z_{2m}, z_{2m+1})$ and the same exchange
matrix. So the sequence $(z_k)$ lists the cluster variables reached by forward alternating mutation.
When $bc \ge 4$ and the initial cluster is algebraically independent, the variables reached by
mutating backwards are not among them; for special initial values they can be, as over
$\mathbb{F}_3$ with $b = c = 2$ and $x = y = 1$, where the sequence $1, 1, 2, 2, \dots$ is periodic.

## Sources

- S. Fomin, L. Williams and A. Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5, Section 3.2: the seed pattern of $\mathcal{A}(b, c)$ and its exchange relations (3.2.2).
