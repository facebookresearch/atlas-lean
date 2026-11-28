# Constant-gap 2CSP is in PromisePCP(log n, 1)

Fix a finite nonempty alphabet $\Sigma$ and a constant $c \in (0, 1]$. Let $\mathrm{Gap2CSP}_{\Sigma, c}$ be the promise problem whose yes-instances are satisfiable well-formed binary constraint graphs over $\Sigma$ (given by vertex count, edge list and full constraint tables) and whose no-instances are well-formed graphs in which every labelling violates at least a $c$ fraction of the edges. Then $\mathrm{Gap2CSP}_{\Sigma, c} \in \mathrm{PromisePCP}(\log n + 1, 1)$.

## Proof sketch

A proof gives each vertex its label in one-hot form of width $|\Sigma|$. One round samples an edge with fair bits from a power-of-two range (accepting padding indices) and checks its constraint with $2|\Sigma|$ queries; on a no-instance it rejects with probability at least $c/2$, and a constant number of independent rounds brings soundness to $1/2$.

## Depends on

- [Promise class PCP(r, q)](promise-class-pcp.md)
- [2CSP instances](../dinur-s-gap-amplification/cspinstance.md)

## Proof depends on

- [The random-edge verifier rejects with probability at least half the gap](random-edge-verifier-soundness.md)
- [Independent repetition multiplies acceptance probabilities](independent-repetition-of-local-tests.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
