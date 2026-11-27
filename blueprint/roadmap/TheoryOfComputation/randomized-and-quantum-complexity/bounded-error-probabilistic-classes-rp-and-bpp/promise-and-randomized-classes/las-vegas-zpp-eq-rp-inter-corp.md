# Expected polynomial-time zero-error computation equals RP ∩ coRP

Let $\mathsf{ZPP}_{\mathrm{exp}}=\bigcup_d\mathsf{ZTIME}(n^d)$ be the class of languages decided by a fair-coin machine that halts with probability $1$, always outputs the correct answer when it halts, and has expected running time $O(n^d)$ on every input. Then $\mathsf{ZPP}_{\mathrm{exp}}=\mathsf{RP}\cap\mathsf{coRP}$.

## Proof sketch

Truncating a Las Vegas machine at twice its expected time and outputting a default answer gives, by Markov's inequality, one-sided error $1/2$ in both directions. Conversely, alternate the RP and coRP algorithms until one gives a certain answer; each round succeeds with probability $\ge1/2$, so the expected number of rounds is at most $2$.

## Depends on

- [The class RP](../../../complexity-classes/time-and-space-complexity-classes/rp.md)
- [The class coRP](../../../complexity-classes/time-and-space-complexity-classes/co-rp.md)
- [ZPP](../../../complexity-classes/time-and-space-complexity-classes/zpp.md)

## Proof depends on

- [ZPP is the intersection of RP and coRP](../../../complexity-classes/time-and-space-complexity-classes/zpp-eq.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 7 (Theorem 7.8 and Exercise 7.4 of the January 2007 web draft, with $\mathsf{ZPP}=\bigcup_c\mathsf{ZTIME}(n^c)$ defined by expected running time).
- John Gill, "Computational Complexity of Probabilistic Turing Machines", SIAM Journal on Computing 6(4), 675–695, 1977.
