# Adjacent-pair block functions: sensitivity Θ(√n), block sensitivity Θ(n)

For $n \ge 4$, split $[n]$ into $k = \lfloor \sqrt n \rfloor$ balanced contiguous blocks and let $f$ be the OR over blocks of the predicate "the block contains exactly two true bits, and they are adjacent". Then

$$\sqrt n \le s(f) \le 3\sqrt n, \qquad n \le 3\, bs(f), \qquad bs(f) \le C(f) \le D(f) \le n.$$

For an arbitrary layout into $k$ consecutive blocks of at most $M$ bits, $s(f) \le \max(3k, M)$ and $\sum_{\text{blocks } B} \lfloor |B|/2 \rfloor \le bs(f)$. Hence block sensitivity can be quadratically larger than sensitivity. This is a variant of Rubinstein's function, which instead accepts a block when its true bits are exactly one of the fixed pairs $\{2j-1, 2j\}$; the bounds above are derived for the variant on this page.

## Proof sketch

At the all-zero input each pair of adjacent positions in a block is a sensitive block, giving about $n/2$ disjoint sensitive blocks. Sensitivity: if exactly one block accepts, every position of that block is sensitive (flipping a $0$ there gives three true bits, flipping a $1$ leaves one), and no position outside it is; this gives $s(f) \le M$ on such inputs and, at a block of about $n/k \ge \sqrt n$ positions, the lower bound $s(f) \ge \sqrt n$. If two or more blocks accept, no single flip changes $f$. If no block accepts, each block has at most three sensitive positions, at most $3k$ in total.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- D. Rubinstein, "Sensitivity vs. Block Sensitivity of Boolean Functions", Combinatorica 15(2), 1995.
