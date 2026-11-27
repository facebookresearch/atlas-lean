# Halting 0-trees of different catalytic contents are disjoint and cover all reachable configurations

Let $M$ be a valid catalytic machine and $x$ an input, with the notation $T(h)$ for halting 0-trees. Then:

1. each tree of $\mathcal{G}^0_{M,x}$ contains at most one halting configuration;
2. for distinct $\tau\ne\tau'\in\{0,1\}^c$ the four vertex sets $T(\mathrm{acc}_\tau)$, $T(\mathrm{rej}_\tau)$, $T(\mathrm{acc}_{\tau'})$, $T(\mathrm{rej}_{\tau'})$ are pairwise disjoint;
3. every configuration reachable from $\mathrm{start}_\tau$ under some choice sequence lies in $T(\mathrm{acc}_\tau)\cup T(\mathrm{rej}_\tau)$.

## Proof sketch

Halting configurations have no outgoing edges, and following the unique outgoing $0$-edge from any vertex of a tree ends at its unique sink, so a tree has at most one halting vertex; the halting configurations $\mathrm{acc}_\tau,\mathrm{rej}_\tau,\mathrm{acc}_{\tau'},\mathrm{rej}_{\tau'}$ are distinct, which gives disjointness. For coverage, if $v$ is reached from $\mathrm{start}_\tau$ by choices $\sigma$, run the choice sequence $\sigma 0^\ast$: validity forces it to halt with the catalytic tape restored to $\tau$, i.e. in $\mathrm{acc}_\tau$ or $\mathrm{rej}_\tau$, and the suffix after $v$ uses only $0$-edges, so $v$ lies in the corresponding halting tree.

## Depends on

- [Configuration graphs and halting 0-trees of a catalytic machine](configuration-graphs-and-halting-zero-trees.md)
- [Valid catalytic machines with nondeterministic or random choices](valid-catalytic-machines-with-choices.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
