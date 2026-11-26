# Adjacent-pair block functions: sensitivity Θ(√n), block sensitivity Θ(n)

For $n \ge 4$, split $[n]$ into $k = \lfloor \sqrt n \rfloor$ balanced contiguous blocks and let $f$ be the OR over blocks of the predicate "the block contains exactly two true bits, and they are adjacent". Then

$$\sqrt n \le s(f) \le 3\sqrt n, \qquad n \le 3\, bs(f), \qquad bs(f) \le C(f) \le D(f) \le n.$$

For an arbitrary layout into $k$ consecutive blocks of at most $M$ bits, $s(f) \le \max(3k, M)$ and $\sum_{\text{blocks } B} \lfloor |B|/2 \rfloor \le bs(f)$. Hence block sensitivity can be quadratically larger than sensitivity (Rubinstein's phenomenon).

## Proof sketch

At the all-zero input each pair of adjacent positions in a block is a sensitive block, giving about $n/2$ disjoint sensitive blocks. Sensitivity is small: if some block accepts, only its at most three relevant positions are sensitive; if none accepts, each block contributes at most a constant number of sensitive positions plus possibly its own size.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- D. Rubinstein, "Sensitivity vs. Block Sensitivity of Boolean Functions", Combinatorica 15(2), 1995.
