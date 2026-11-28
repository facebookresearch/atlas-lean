# Reversible Euler-tour exploration of halting 0-trees in catalytic space O(s)

Fix a rotation map $\mathrm{ROT}^0$ on the 0-graph of a catalytic machine $M$ (free space $s$, catalytic space $c$) in which the outgoing $0$-edge of a vertex has index $0$, and let $\mathrm{NEXT}(v,i)=(u,j+1\bmod \deg u)$ when $\mathrm{ROT}^0(v,i)=(u,j)$, which walks an Euler tour of the component of $v$. Let $S=2^{O(s)}$. There are catalytic subroutines using $O(s)$ additional work space, operating in place on a configuration stored on the catalytic and work tapes, such that:

- $\mathrm{WALK}(h,t)$, for a halting configuration $h$ and $t\le S$, replaces $(h,0)$ by the edge reached after $t$ applications of $\mathrm{NEXT}$;
- $\mathrm{COUNTSTEPSBACK}$, from an edge $e$, applies the inverse of $\mathrm{NEXT}$ until it first reaches an edge $(h,0)$ with $h$ halting; it restores $(h,0)$ and outputs the number $\ell\le S$ of backward steps taken, or reports $\infty$ if no such edge is reached within $S$ backward steps. It therefore inverts $\mathrm{WALK}(h,t)$ only when the walk does not return to $(h,0)$ within $t$ steps, i.e. when $t$ is less than the length $2|E(T(h))|$ of one Euler tour of $T(h)$: on a one-edge tree, $t=1$ and $t=3$ reach the same edge. This holds for every $t\le S$ in the large-tree case $|T(h)|>S/2+1$ used for compression;
- $\mathrm{SIZE}(h)$ outputs twice the number of edges of $T(h)$ when $2\le |T(h)|\le S/2+1$, and $1$ or $\infty$ otherwise, leaving $h$ in place.

## Proof sketch

A single transition of $M$ and its possible predecessors are determined locally by the finite control and the tape cells under the heads, so $\mathrm{ROT}^0$ can be applied in place and inverted using $O(s)$ work space. An Euler tour of a tree driven by a rotation map is reversible step by step (Lange–McKenzie–Tapp style), so iterating $\mathrm{NEXT}$ with an $O(\log S)=O(s)$-bit counter, or iterating its inverse until the edge $(h,0)$ of a halting configuration $h$ (recognizable from the work tape) appears, implements the three subroutines without ever storing more than one configuration.

## Depends on

- [Configuration graphs and halting 0-trees of a catalytic machine](configuration-graphs-and-halting-zero-trees.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019 (§4.3, Lemma 24).
