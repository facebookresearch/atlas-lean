# The class QCMA of quantum verification with classical witnesses

A promise problem $(L_{yes}, L_{no})$ is in $\mathrm{QCMA}$ if there is a polynomial-time uniform family of quantum verifier circuits $V_x$ taking a classical witness $w \in \{0,1\}^{p(|x|)}$ such that: for $x \in L_{yes}$ some $w$ makes $V_x$ accept with probability at least $2/3$; for $x \in L_{no}$ every $w$ makes $V_x$ accept with probability at most $1/3$. Clearly $\mathrm{MA} \subseteq \mathrm{QCMA} \subseteq \mathrm{QMA}$.

## Depends on

- [QMA for promise problems](../../local-hamiltonian-problem/qmapromise.md)
- [BQP](../../../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Sources

- Scott Aaronson, Greg Kuperberg, "Quantum versus classical proofs and advice", Theory of Computing 3 (2007), CCC (2007); arXiv:quant-ph/0604056.
