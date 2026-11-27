# Rigidity of near-optimal CHSH strategies

Let a tensor strategy for the CHSH game use $\pm 1$-valued observables $A_0, A_1$ for Alice and $B_0, B_1$ for Bob on a state $\psi$, and suppose it wins with probability at least $\cos^2(\pi/8) - \varepsilon$. Then Alice's observables approximately anticommute on the state:

$$\big\| (A_0 A_1 + A_1 A_0) \otimes 1 \cdot \psi \big\| \le C \sqrt{\varepsilon}$$

for an absolute constant $C$ and every $\varepsilon \ge 0$, and symmetrically for Bob. Equivalently the squared norm is $O(\varepsilon)$. A winning probability $\cos^2(\pi/8) - \varepsilon$ is a CHSH value $\langle\psi, (A_0B_0 + A_0B_1 + A_1B_0 - A_1B_1)\psi\rangle \ge 2\sqrt2 - 8\varepsilon$, and McKague, Yang and Scarani bound the norm by $4(8\sqrt2\,\varepsilon)^{1/2}$ when $0 < 8\varepsilon < 1$ (Theorem 2 with condition (3) of Theorem 1), which for $\varepsilon = 0$ gives norm $0$ by applying it with every positive deficit; for $8\varepsilon \ge 1$ the bound holds trivially once $C \ge 2\sqrt8$, since the norm is at most $2$.

## Proof sketch

Write the CHSH bias as $\langle\psi, \mathcal{B}\psi\rangle$ with $\mathcal{B} = \sum_{x,y} (-1)^{xy} A_x \otimes B_y / 4$. A sum-of-squares decomposition $2\sqrt2 - \mathcal{B}' = \frac{1}{\sqrt2}\sum_i S_i^* S_i$ shows that a small deficit forces $\|S_i\psi\|$ small, and these vanishing combinations express Bob's operators through Alice's in a way that implies approximate anticommutation.

## Depends on

- [Classical and entangled values of the CHSH game](../../../../QuantumInformation/quantum-foundations/classical-and-entangled-values-of-the-chsh-game.md)
- [Entangled strategies and the entangled value of a game](entangled-strategies-and-entangled-value.md)

## Sources

- M. McKague, T. H. Yang and V. Scarani, "Robust Self-Testing of the Singlet", Journal of Physics A 45(45), 2012; arXiv:1203.2976, Theorems 1 and 2.
- A. Natarajan and T. Vidick, "A Quantum Linearity Test for Robustly Verifying Entanglement", STOC 2017.
- J. F. Clauser, M. A. Horne, A. Shimony and R. A. Holt, "Proposed Experiment to Test Local Hidden-Variable Theories", Physical Review Letters 23(15), 1969.
