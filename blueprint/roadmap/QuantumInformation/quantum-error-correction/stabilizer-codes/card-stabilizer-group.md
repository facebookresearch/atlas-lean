# Independent generators give 2^r stabilizer elements

Let $g_1, \dots, g_r$ be signed Pauli operators on $n$ qubits, $g_j = c_j X^{a_j} Z^{b_j}$ with $a_j, b_j \in \mathbb{F}_2^n$ and $c_j \in \mathbb{C}$ that are involutive ($g_j^2 = I$) and pairwise commuting, and whose Pauli labels $(a_j, b_j) \in \mathbb{F}_2^{2n}$ are linearly independent over $\mathbb{F}_2$. Then the $2^r$ subset products $\prod_{j \in T} g_j$,
$T \subseteq \{1, \dots, r\}$, are pairwise distinct: the [set of subset products](stabilizer-group.md) has exactly $2^r$ elements.
