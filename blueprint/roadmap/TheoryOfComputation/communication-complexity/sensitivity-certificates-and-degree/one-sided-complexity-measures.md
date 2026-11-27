# One-sided sensitivity, block sensitivity and certificate complexity

For $f : \{0,1\}^n \to \{0,1\}$ and $b \in \{0,1\}$, the *$b$-sensitivity* is $s_b(f) = \max_{x \in f^{-1}(b)} s(f, x)$, and similarly $bs_b(f) = \max_{x \in f^{-1}(b)} bs(f, x)$ and $C_b(f) = \max_{x \in f^{-1}(b)} C(f, x)$ (as on the linked page), each maximum being $0$ when $f$ never takes the value $b$. Then $s(f) = \max(s_0, s_1)$, $bs(f) = \max(bs_0, bs_1)$, $C(f) = \max(C_0, C_1)$, and negating $f$ swaps the indices $0$ and $1$ while preserving each two-sided measure.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002.
- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
