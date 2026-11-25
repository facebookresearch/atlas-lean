# Edge product of a glued configuration factorizes

Let $d, n \in \mathbb{N}$, let $\Lambda_m = \{-m, \dots, m\}^d$ carry its nearest-neighbour edges (so $\Lambda_n \subseteq \Lambda_{n+1}$), and let $\psi$ be an assignment of open/closed states to the unordered pairs of vertices of $\Lambda_{n+1}$ (the outer configuration), and $\omega$ one for the unordered pairs of vertices of $\Lambda_n$, and let $p \in \mathbb{R}$. Then

$$\pi_{\Lambda_{n+1}}(\psi \oplus \omega) = \pi_{\Lambda_n}(\omega)\, \pi^{\mathrm{out}}(\psi),$$

where $\pi_G(\eta) = \prod_{e \in E(G)} (p \text{ if } e \text{ is open in } \eta,\ 1 - p \text{ otherwise})$ is the [Bernoulli edge product](../../random-cluster-measures-on-finite-graphs/edge-product.md), $\psi \oplus \omega$ is the [glued configuration](psi-ext.md) (the pairs with both endpoints in $\Lambda_n$ take their state from $\omega$, all other pairs from $\psi$), and $\pi^{\mathrm{out}}(\psi)$ is the [outer edge factor](psi-edge-factor.md), the same product over the edges of $\Lambda_{n+1}$ that do not have both endpoints in $\Lambda_n$.
