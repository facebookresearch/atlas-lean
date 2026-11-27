# Optimal QMAM acceptance probability as an exponential-size semidefinite program

For a QMAM protocol on inputs of length $n$, the maximum acceptance probability over all provers equals the optimal value of a semidefinite program over density operators on $\mathsf{X}\mathsf{Y}$ (dimension $D = 2^{\mathrm{poly}(n)}$) of the form

$$
\max_{\rho_0, \rho_1} \ \tfrac12 \left( \langle \Pi_0, \rho_0 \rangle + \langle \Pi_1, \rho_1 \rangle \right) \quad \text{subject to } \mathrm{Tr}_{\mathsf{Y}} \rho_0 = \mathrm{Tr}_{\mathsf{Y}} \rho_1,
$$

whose input matrices $\Pi_0, \Pi_1$ have entries computable by $\mathrm{NC}(\mathrm{poly})$ circuits from the verifier's description.

## Proof sketch

Merlin's first message fixes the reduced state of $\mathsf{X}$; by Uhlmann's theorem, after seeing $b$ Merlin can transform any purification so that the joint state of $\mathsf{X}\mathsf{Y}$ is any $\rho_b$ with that reduced state. Averaging the acceptance probabilities over $b$ gives the stated program. The projectors are products of polynomially many gates, each a sparse $D \times D$ matrix, so their entries are computed by iterated matrix multiplication in polynomial depth.

## Depends on

- [The class NC(poly) of polynomial-depth bounded fan-in circuit families](polynomial-depth-circuit-class-nc-poly.md)
- [Quantum Merlin-Arthur-Merlin games (QMAM)](quantum-merlin-arthur-merlin-games.md)

## Proof depends on

- [Marriott-Watrous: QIP equals QMAM](marriott-watrous-qip-equals-qmam.md)

## Sources

- Rahul Jain, Zhengfeng Ji, Sarvagya Upadhyay, John Watrous, "QIP = PSPACE", Journal of the ACM 58(6) (2011), STOC (2010); arXiv:0907.4737.
- Rahul Jain, Sarvagya Upadhyay, John Watrous, "Two-message quantum interactive proofs are in PSPACE", FOCS (2009); arXiv:0905.1300.
