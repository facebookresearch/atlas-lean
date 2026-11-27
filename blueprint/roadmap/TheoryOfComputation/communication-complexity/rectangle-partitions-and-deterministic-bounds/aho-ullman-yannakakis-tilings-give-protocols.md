# Aho–Ullman–Yannakakis: tilings give O(log² χ) protocols

If a function $f : X \times Y \to Z$ has a labelled rectangle partition with $t$ rectangles, then it has a deterministic protocol of depth at most $2 \lceil \log_2 t \rceil \lceil \log_2 (t+1) \rceil$. Hence, for Boolean $f$ (so that $D(f)$ is the complexity of the linked page),

$$D(f) \le 8 \big(\log_2 \chi(f)\big)^2 + O(1),$$

so deterministic communication complexity and the logarithm of the tiling number are polynomially (quadratically) related.

## Proof sketch

Two disjoint rectangles share rows, or share columns, or neither, but not both: the singletons $\{(0,0)\}$ and $\{(1,1)\}$ share neither. So for the rectangle $R^*$ containing the input, the other remaining rectangles that share rows with $R^*$ and those that share columns with $R^*$ are disjoint families, and one of them has at most half of them. In each round Alice either names a remaining rectangle containing her row that shares rows with at most half of the other remaining rectangles, or announces that there is none, in $\lceil \log_2(t+1) \rceil$ bits; in the second case Bob names such a rectangle for columns in $\lceil \log_2 t \rceil$ bits. Both keep only the rectangles sharing rows (resp. columns) with the named one, which still contain $R^*$, so the list shrinks from $s$ to at most $\lceil s/2 \rceil$; after $\lceil \log_2 t \rceil$ rounds one rectangle, and its label, remains.

## Depends on

- [Monochromatic rectangle partitions and the tiling number](monochromatic-rectangle-partitions-and-tiling-number.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Sources

- A. V. Aho, J. D. Ullman and M. Yannakakis, "On Notions of Information Transfer in VLSI Circuits", STOC 1983.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
