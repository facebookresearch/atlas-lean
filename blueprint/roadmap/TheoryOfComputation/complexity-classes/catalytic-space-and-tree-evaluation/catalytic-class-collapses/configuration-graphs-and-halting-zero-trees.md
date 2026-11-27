# Configuration graphs and halting 0-trees of a catalytic machine

Fix a valid catalytic machine $M$ with free space $s$ and catalytic space $c$ and an input $x$; assume the finite-control state and all head positions are recorded in a designated part of the work tape. A configuration is a pair $\langle\pi,u\rangle$ with $\pi\in\{0,1\}^c$ the catalytic content and $u\in\{0,1\}^s$ the work content. Normalize $M$ so that from initial content $\tau$ it starts in $\mathrm{start}_\tau=\langle\tau,0^s\rangle$ and halts only in $\mathrm{acc}_\tau=\langle\tau,110^{s-2}\rangle$ or $\mathrm{rej}_\tau=\langle\tau,100^{s-2}\rangle$.

The configuration graph $\mathcal{G}_{M,x}$ is the directed graph on all configurations with an edge from $v$ to $v'$ when $v'$ follows $v$ in one step; each edge is labeled by the choice bit(s) that produce it (deterministic steps carry both labels). Every vertex has out-degree at most $2$ and in-degree bounded by a constant $d_M$. The **0-graph** $\mathcal{G}^0_{M,x}$ is the undirected graph keeping only edges labeled $0$. Since every vertex has at most one outgoing $0$-edge and valid machines never loop, each connected component of $\mathcal{G}^0_{M,x}$ containing a halting configuration $h$ is a tree, denoted $T(h)$, and $T(h)$ consists of all configurations from which running with all-zero choices reaches $h$.

## Depends on

- [Valid catalytic machines with nondeterministic or random choices](valid-catalytic-machines-with-choices.md)
- [Configuration graph of a space-bounded machine](../../space-and-time-complexity/configuration-graph-of-a-space-bounded-machine.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
