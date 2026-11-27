# Delta-matroids and even delta-matroids

A nonempty Boolean relation $R \subseteq \{0,1\}^n$ is a *delta-matroid* if for all $x, y \in R$ and every coordinate $i$ with $x_i \ne y_i$ there is a coordinate $j$ with $x_j \ne y_j$ such that $x \oplus e_{\{i,j\}} \in R$, where $e_{\{i,j\}}$ is the indicator vector of the set $\{i,j\}$ (so $j = i$ is allowed, and then only coordinate $i$ is flipped). It is an *even delta-matroid* if all its tuples have the same parity of Hamming weight (then necessarily $j \ne i$). A relation is *self-complementary* if it is closed under flipping all coordinates of a tuple simultaneously. The *cyclic difference* of a tuple $x \in \{0,1\}^n$ is $(x_1 \oplus x_2, x_2 \oplus x_3, \dots, x_n \oplus x_1)$; the relation $dR$ consists of the cyclic differences of tuples of $R$, and all its tuples have even weight. The exactly-one relations and the nonempty parity relations are even delta-matroids; the empty relation is not a delta-matroid.

## Depends on

- [Boolean constraint languages and CSP(Γ)](../../boolean-constraint-satisfaction/polymorphisms-of-boolean-relations/boolean-constraint-languages.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019, Definitions 5, 13 and 14.
- Z. Dvořák and M. Kupec, "On Planar Boolean CSP", Automata, Languages, and Programming — ICALP 2015, Part I, LNCS 9134, 432–443, 2015.
