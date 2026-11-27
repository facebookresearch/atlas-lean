# Synchronous two-prover games

A two-prover one-round game $G = (\mathcal{X}, \mathcal{X}, \mathcal{A}, \mathcal{A}, \mu, V)$ is *synchronous* if $\mu$ is symmetric, every $x$ with $\mu_A(x) := \sum_y \mu(x, y) > 0$ satisfies $\mu(x, x) > 0$, and $V(x, x, a, b) = 0$ whenever $a \ne b$. A finite-dimensional strategy $(\psi, \{A^x_a\}, \{B^x_b\})$ is *synchronous* if $\psi$ is the maximally entangled state $\frac{1}{\sqrt d}\sum_i |i\rangle|i\rangle$, every $A^x_a$ is a projection and $B^x_a = \overline{A^x_a}$; its value equals $\sum_{x,y}\mu(x,y)\sum_{a,b} V(x,y,a,b)\, \tau(A^x_a A^y_b)$ with $\tau = \frac1d \mathrm{Tr}$ the normalized trace. The *synchronous value* $\omega^*_s(G)$ is the supremum of values of synchronous strategies.

## Depends on

- [Uniformly generated families of two-prover one-round games](uniformly-generated-game-families.md)
- [Two-player nonlocal games: classical and entangled values](../../../../QuantumInformation/quantum-foundations/two-player-nonlocal-games-classical-and-entangled-values.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
- Se-Jin Kim, Vern Paulsen, Christopher Schafhauser, "A synchronous game for binary constraint systems", Journal of Mathematical Physics 59 (2018); arXiv:1707.01016.
