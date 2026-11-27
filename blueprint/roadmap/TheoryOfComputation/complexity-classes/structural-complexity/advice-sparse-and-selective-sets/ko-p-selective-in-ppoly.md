# Ko: P-selective sets are in P/poly

Every P-selective set $A$ is in $\mathsf{P}/\mathrm{poly}$; more precisely, at length $n$ a set of at most $n+1$ members of $A\cap\{0,1\}^n$ suffices as advice, giving $O(n^2)$ advice bits.

## Proof sketch

Fix a selector $f$ and $n$, and say $x$ beats $y$ when $f(x,y)=x$. If $y\in A$ and $x$ beats $y$ then $x\in A$. Greedily choose $D\subseteq A\cap\{0,1\}^n$: pick a member beaten by at least half of the remaining members (it exists by averaging over the tournament) and discard those that beat it; after at most $n+1$ rounds every member of $A\cap\{0,1\}^n$ is in $D$ or beats some element of $D$. Then $x\in A$ iff $x\in D$ or $x$ beats some $y\in D$, which is checkable in polynomial time from the advice $D$.

## Depends on

- [P-selective sets](p-selective-sets.md)
- [Polynomial time with polynomial advice](../../time-and-space-complexity-classes/ppoly.md)

## Sources

- Ker-I Ko, "On Self-Reducibility and Weak P-Selectivity", Journal of Computer and System Sciences 26(2), 1983.
- Lane A. Hemaspaandra and Leen Torenvliet, "Theory of Semi-Feasible Algorithms", Springer, 2003.
