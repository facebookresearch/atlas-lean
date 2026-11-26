# Exact deterministic complexity of equality on a finite set

For every finite set $X$ with $|X| \ge 2$, the deterministic communication complexity (with both players learning the answer) of equality $\mathrm{EQ}_X(x, y) = [x = y]$ is exactly $\lceil \log_2 |X| \rceil + 1$. For $n$-bit strings this is $n + 1$. Greater-than, inner product modulo two, disjointness, intersection and inclusion of $n$-bit strings also have complexity exactly $n + 1$ for $n \ge 1$.

## Proof sketch

Upper bound: Alice sends her element in $\lceil\log_2|X|\rceil$ bits and Bob announces the answer. Lower bound: if a protocol computes equality on a rectangle $A \times B$ containing a pair of distinct elements, induction on the first bit gives $2|A \cap B| \le 2^d$; this is sharper than the fooling-set bound when $|X|$ is not a power of two. The other functions have fooling sets of size $2^n$ (or full-rank matrices) plus one bit to announce.

## Depends on

- [Equality function](../deterministic-communication-protocols/eq-fn.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Proof depends on

- [Fooling-set lower bound](../deterministic-communication-protocols/card-le-two-pow-of-is-fooling-set.md)
- [Deterministic communication complexity of equality](../deterministic-communication-protocols/comm-complexity-eq-fn.md)

## Sources

- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
