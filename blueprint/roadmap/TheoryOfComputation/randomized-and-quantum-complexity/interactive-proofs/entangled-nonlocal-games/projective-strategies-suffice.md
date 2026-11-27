# Projective strategies suffice (Naimark dilation)

For every finite-dimensional entangled strategy with POVM measurements there is a finite-dimensional strategy with projective measurements, on larger local spaces, that produces exactly the same correlation $p(a, b \mid x, y)$. Hence $\mathrm{val}^*(G)$ is the supremum over projective strategies, and agreement relations between measurements are preserved by the dilation.

## Proof sketch

Naimark's theorem dilates each POVM $\{P_a\}$ on $H$ to a projective measurement $\{\Pi_a\}$ on $H \otimes \mathbb{C}^A$ with $P_a = V^* \Pi_a V$ for the isometry $V\phi = \sum_a \sqrt{P_a}\phi \otimes e_a$. Since $V = V_x$ depends on the question, extend each $V_x$ to a unitary $U_x$ on $H \otimes \mathbb{C}^A$ with $U_x(\phi \otimes e_{a_0}) = V_x \phi$, set $\Pi^x_a = U_x^* (1 \otimes |e_a\rangle\langle e_a|) U_x$, and append the fixed ancilla $e_{a_0}$ on each side; doing this locally for both parties preserves all joint probabilities.

## Depends on

- [Entangled strategies and the entangled value of a game](entangled-strategies-and-entangled-value.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "MIP* = RE", arXiv:2001.04383, 2020.
- A. Natarajan and T. Vidick, "A Quantum Linearity Test for Robustly Verifying Entanglement", STOC 2017.
