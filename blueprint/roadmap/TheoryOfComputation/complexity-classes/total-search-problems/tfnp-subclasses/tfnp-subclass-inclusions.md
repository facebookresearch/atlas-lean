# Inclusions among the TFNP subclasses

$\mathsf{PPAD}\subseteq\mathsf{PPADS}\subseteq\mathsf{PPP}\subseteq\mathsf{TFNP}$, $\mathsf{PPAD}\subseteq\mathsf{PPA}\subseteq\mathsf{TFNP}$ and $\mathsf{PLS}\subseteq\mathsf{TFNP}$.

## Proof sketch

END-OF-LINE reduces to SINK-OF-LINE by taking solutions without an outgoing arc, and SINK-OF-LINE to PIGEON via the circuit sending $x$ to $S(x)$ when $x\to S(x)$ is an arc and to $x$ itself otherwise: nothing maps to $0^n$, and every collision involves a sink. Forgetting arc directions reduces END-OF-LINE to LEAF.

## Depends on

- [The classes PPP, PPAD, PPADS and PPA](ppp-ppad-ppads-ppa.md)
- [The class PLS of polynomial local search problems](../the-class-pls-of-polynomial-local-search.md)

## Proof depends on

- [END-OF-THE-LINE is total](../../../completeness-other-classes/ppad-and-the-end-of-the-line-problem/exists-solution.md)

## Sources

- Paul Beame et al., "The Relative Complexity of NP Search Problems", Journal of Computer and System Sciences 57(1), 1998.
- Christos H. Papadimitriou, "On the Complexity of the Parity Argument and Other Inefficient Proofs of Existence", Journal of Computer and System Sciences 48(3), 1994.
