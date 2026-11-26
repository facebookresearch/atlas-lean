# Koucký–Mertz–Pyne–Sami compute-or-compress lemma for catalytic configuration graphs

Let $M$ be a valid catalytic machine with free space $s$ and catalytic space $c$, $\log n\le s\le c\le 2^s$, and fix an input $x$. Let $B=2s$ and $S=2^B$. Suppose the catalytic tape holds $\tau\in\{0,1\}^c$ followed by an extra block $\mathrm{tar}\in\{0,1\}^B$. There is a catalytic subroutine $\mathrm{COMPUTEORCOMPRESS}(\tau,\mathrm{tar})$ using $O(s)$ additional work space that takes exactly one of two actions and reports which:

1. **Compute.** If $|T(\mathrm{acc}_\tau)|\le S/2+1$ and $|T(\mathrm{rej}_\tau)|\le S/2+1$, it outputs a directed graph $G$ on at most $S+2$ vertices and vertices $r,t$ such that the subgraph forward-reachable from $r$ is isomorphic to the reachable configuration graph $\mathcal{G}_{M,x,\tau}$, with $\mathrm{start}_\tau\mapsto r$ and $\mathrm{acc}_\tau\mapsto t$ and edge labels preserved; the catalytic tape is unchanged.
2. **Compress.** Otherwise, it replaces $\tau$ by some $\pi\in\{0,1\}^c$ and $\mathrm{tar}$ by $(u,j,0^{B-s-\lceil\log d_M\rceil})$ with $u\in\{0,1\}^s$, $j\in[d_M]$, such that $\mathrm{COUNTSTEPSBACK}(\langle\pi,u\rangle,j)$ restores $\tau$ and outputs exactly $\mathrm{tar}$.

In the compress case roughly $s$ catalytic bits become zero, i.e. free.

## Proof sketch

Call $\mathrm{SIZE}$ on $\mathrm{acc}_\tau$ and $\mathrm{rej}_\tau$, which are computable from $\tau$. If both trees are small, enumerate their vertices by Euler-tour index with $\mathrm{WALK}$ and write the graph induced on their union, which contains every reachable configuration by the covering lemma. If, say, $T(\mathrm{acc}_\tau)$ is large, interpret $\mathrm{tar}$ as a time $t\le S$ and run $\mathrm{WALK}(\mathrm{acc}_\tau,t)$: the resulting edge $(\langle\pi,u\rangle,j)$ is described with $c+s+O(1)$ bits instead of $c+B$, and walking back with $\mathrm{COUNTSTEPSBACK}$ recovers both $\tau$ and $t=\mathrm{tar}$ because the tour has more than $S$ steps and hence no earlier return to a halting configuration.

## Depends on

- [Configuration graphs and halting 0-trees of a catalytic machine](configuration-graphs-and-halting-zero-trees.md)
- [Valid catalytic machines with nondeterministic or random choices](valid-catalytic-machines-with-choices.md)

## Proof depends on

- [Reversible Euler-tour exploration of halting 0-trees in catalytic space O(s)](reversible-euler-tour-of-halting-trees.md)
- [Halting 0-trees of different catalytic contents are disjoint and cover all reachable configurations](halting-zero-trees-disjoint-and-covering.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
