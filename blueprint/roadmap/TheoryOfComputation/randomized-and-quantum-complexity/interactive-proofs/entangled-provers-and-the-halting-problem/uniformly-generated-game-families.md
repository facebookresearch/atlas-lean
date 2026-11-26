# Uniformly generated families of two-prover one-round games

A *two-prover one-round game* $G = (\mathcal{X}, \mathcal{Y}, \mathcal{A}, \mathcal{B}, \mu, V)$ consists of finite question sets $\mathcal{X}, \mathcal{Y}$, finite answer sets $\mathcal{A}, \mathcal{B}$, a probability distribution $\mu$ on $\mathcal{X} \times \mathcal{Y}$ and a decision predicate $V : \mathcal{X} \times \mathcal{Y} \times \mathcal{A} \times \mathcal{B} \to \{0, 1\}$. Its entangled value $\omega^*(G)$ is the supremum, over all finite dimensions $d$, states $\psi \in \mathbb{C}^d \otimes \mathbb{C}^d$ and POVMs $\{A^x_a\}_a$, $\{B^y_b\}_b$ on $\mathbb{C}^d$, of

$$
\sum_{x, y} \mu(x, y) \sum_{a, b} V(x, y, a, b) \, \langle \psi | A^x_a \otimes B^y_b | \psi \rangle .
$$

A family $(G_z)_{z \in \{0,1\}^*}$ is *uniformly generated* if question and answer strings have length $\mathrm{poly}(|z|)$ and there are polynomial-time Turing machines $Q$ and $D$ such that $Q(z, r)$, on uniformly random $r \in \{0,1\}^{\mathrm{poly}(|z|)}$, outputs a pair distributed as $\mu_z$, and $D(z, x, y, a, b) = V_z(x, y, a, b)$.

## Depends on

- [Two-player nonlocal games: classical and entangled values](../../../../QuantumInformation/quantum-foundations/two-player-nonlocal-games-classical-and-entangled-values.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
- Joseph Fitzsimons, Zhengfeng Ji, Thomas Vidick, Henry Yuen, "Quantum proof systems for iterated exponential time, and beyond", STOC (2019); arXiv:1805.12166.
