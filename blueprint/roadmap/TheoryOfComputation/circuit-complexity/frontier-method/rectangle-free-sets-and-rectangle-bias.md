# Rectangle-free sets and rectangle bias

Let $U$ be a finite alphabet and $\iota$ a finite set of coordinates. A set $X\subseteq\iota$ cuts an input $x\in U^\iota$ into $(x|_X,x|_{\iota\setminus X})$. A *combinatorial rectangle* (with respect to $X$) is a set $A\times B$ with $A\subseteq U^X$, $B\subseteq U^{\iota\setminus X}$. A set $S\subseteq U^\iota$ is *$K$-rectangle-free* if it contains no rectangle $A\times B$ (for any cut $X$) with $|A|\ge K$ and $|B|\ge K$. $S$ has *bias at most $b$ on $K$-rectangles* if for every cut and every rectangle with both sides of size at least $K$, the density of $S$ in the rectangle is within $b$ of $\tfrac12$.

## Depends on

- [Rectangle lemma](../../communication-complexity/deterministic-communication-protocols/transcript-eq-iff.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Noga Alon, Joel H. Spencer, "The Probabilistic Method", Wiley, 2016.
