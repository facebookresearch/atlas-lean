# Trace of the code projector

Let $g_1, \dots, g_r$ be signed Pauli operators on $n$ qubits, $g_j = c_j X^{a_j} Z^{b_j}$ with $a_j, b_j \in \mathbb{F}_2^n$ and $c_j \in \mathbb{C}$ that are involutive ($g_j^2 = I$) and pairwise commuting, and whose Pauli labels $(a_j, b_j) \in \mathbb{F}_2^{2n}$ are linearly independent over $\mathbb{F}_2$. Then the code projector, the average of the distinct subset products of
the $g_j$, has trace $2^{n-r}$.

Without these hypotheses the formula fails: for $n = r = 1$ and the single generator $g_1 = 2I$,
the distinct subset products are $I$ and $2I$, whose average $\tfrac32 I$ has trace $3$, not $1$.
