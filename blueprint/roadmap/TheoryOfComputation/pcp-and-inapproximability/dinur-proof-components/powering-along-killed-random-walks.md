# Powering a constraint graph along killed random walks

Let $G$ be a $d$-regular constraint graph over $\Sigma$ with self-loops, and let $t \ge 1$. In the powered graph $G^{t}$ every vertex $v$ is labelled by a function assigning a value in $\Sigma$ to every vertex at distance at most $t$ from $v$ (its *opinions*), so the alphabet is $\Sigma^{d^{t}}$ up to a constant power. Edges of $G^t$ are random walks of a random length: starting at a uniform vertex, a walk takes a uniform step and stops after each step with probability $1/t$ (a *killed* or *lazy* walk), conditioned to have length at most a fixed multiple of $t$. The edge joining the endpoints $u, w$ is satisfied when, for every edge $(x, y)$ of $G$ on the walk with both ends within distance $t$ of $u$ and $w$ respectively, the opinions of $u$ about $x$ and of $w$ about $y$ satisfy the constraint of $(x,y)$.

## Depends on

- [Spectral expander](../../../GraphTheory/graph-families-and-operations/expander-graphs/is-spectral-expander.md)

## Sources

- J. Radhakrishnan, "Gap Amplification in PCPs Using Lazy Random Walks", ICALP 2006.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007.
