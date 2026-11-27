# Code projector

Let $g_1, \dots, g_r$ be signed Pauli operators on $n$ qubits, $g_j = c_j X^{a_j} Z^{b_j}$ with $a_j, b_j \in \mathbb{F}_2^n$ and $c_j \in \mathbb{C}$. The code projector is the average

$$P = \frac{1}{|G|} \sum_{s \in G} s$$

of the set $G$ of distinct products $\prod_{j \in T} g_j$ over subsets $T \subseteq \{1, \dots, r\}$,
taken in index order. For arbitrary inputs this is only an average of matrices; when the $g_j$ are
involutive and pairwise commuting it is the orthogonal projector onto the code space.
