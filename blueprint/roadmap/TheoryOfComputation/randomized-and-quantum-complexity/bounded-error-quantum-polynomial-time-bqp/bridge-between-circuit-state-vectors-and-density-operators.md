# Bridge between circuit state vectors and density-operator state models

This node collects the correspondence between the vector model of pure states used by circuit
pages and the density-operator model of quantum states, and the compatibility of measurement and
unitary evolution across it.

## Expansion

A sound expansion has separate pages for:

1. **Pure-state embedding.** For a unit vector $u$ of a finite-dimensional complex Euclidean space,
   $uu^*$ is a density operator of rank one, and every rank-one density operator has this form. Two
   unit vectors give the same density operator if and only if they differ by a scalar of modulus one.
2. **Measurement compatibility.** For a measurement $\mu$ (a finite family of positive semidefinite
   operators summing to the identity), the outcome probability $\langle \mu(a), uu^* \rangle$ equals
   $u^* \mu(a) u$; for a projective measurement this is the squared norm of the projection of $u$.
3. **Unitary compatibility.** For a unitary $U$, $(Uu)(Uu)^* = U (uu^*) U^*$, so applying a circuit to
   a vector and applying the corresponding unitary channel to the density operator agree.
4. **Encoded-circuit bridge.** For an $N$-qubit register encoded in the standard basis $(e_x)$ of
   $\mathbb{C}^{2^N}$, indexed by bit strings $x$ with the qubit-to-bit convention of the encoded 2-local gate model, and a
   unit vector $\psi$: the basis-outcome probability $\lvert \psi_x \rvert^2$ equals the probability of the projector
   $e_x e_x^*$ on $\psi \psi^*$; and the acceptance probability, the sum of $\lvert \psi_x \rvert^2$ over the strings whose
   qubit-$0$ bit is $1$, equals the probability of the projector onto qubit $0$ being $1$ on $\psi \psi^*$. Both sides use the
   same coefficient vector.

## Depends on

- [Positive-operator-valued measurements and the Born rule](../../../QuantumInformation/quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)
- [Density matrices, pure states and reduced states](../../../QuantumInformation/quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
- [Encoded 2-local quantum gate](../../complexity-classes/time-and-space-complexity-classes/qgate.md)
- [Acceptance probability of a quantum state](../../complexity-classes/time-and-space-complexity-classes/accept-prob.md)

## Proof depends on

- [A gate-list channel acts as the circuit](../../../QuantumInformation/quantum-operations/quantum-circuits-as-unitary-channels/circuit-channel-vec-state.md): the unitary-compatibility clause for a well-formed gate list on a unit vector
- [Born rule for the output qubit](../../../QuantumInformation/quantum-operations/quantum-circuits-as-unitary-channels/output-povm-measure-vec-state.md): the qubit-0 acceptance identity

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018, Section 2.1
  (pure states, equation (2.12), and the remark that a pure state determines its unit vector only up
  to a scalar of modulus one) and Section 2.3 (measurements). <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
