# GGM-tree evaluation: every vertex value of the GGM tree GGM_T of C on input x is computable in time Õ(|C| log T)

Let $C\colon\{0,1\}^n\to\{0,1\}^{2n}$, let $T\ge 4n$ and let $k$ be least with $2^kn\ge T$. The **GGM tree** $\mathrm{GGM}_T[C]\colon\{0,1\}^n\to\{0,1\}^T$ assigns $v_{0,0}=x$ to the root of a perfect binary tree of height $k$ and, for every vertex, $v_{i+1,2j}=C(v_{i,j})_{[0,n)}$ and $v_{i+1,2j+1}=C(v_{i,j})_{[n,2n)}$; its output is the first $T$ bits of the concatenated leaf values. There is an algorithm that, given $C,T,x$ and a vertex $(i,j)$, computes $v_{i,j}$ in time $\tilde O(|C|\cdot\log T)$. In particular every string in $\mathrm{Im}(\mathrm{GGM}_T[C])$ is the truth table of a function on $\lceil\log T\rceil$ bits with circuit complexity $\tilde O(|C|\cdot\log T)$.

## Proof sketch

Walk from the root to $(i,j)$ along the binary expansion of $j$, applying $C$ once per level and keeping the left or right half; the tree has height $O(\log T)$. Hard-wiring $x$ and $C$ turns this walk into a small circuit for the leaf string.

## Proof depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](../../complexity-classes/tfnp-hierarchies-and-avoidance/range-avoidance-and-explicit-constructions/range-avoidance-problem.md)

## Sources

- Zeyong Li, "Symmetric Exponential Time Requires Near-Maximum Circuit Size: Simplified, Truly Uniform", STOC (2024), arXiv:2310.17762.
- Lijie Chen, Shuichi Hirahara and Hanlin Ren, "Symmetric Exponential Time Requires Near-Maximum Circuit Size", STOC (2024), arXiv:2309.12912.
- Oliver Korten, "The Hardest Explicit Construction", FOCS (2021), arXiv:2106.00875.
