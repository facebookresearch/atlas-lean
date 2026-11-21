# Factorization of the edge weight of a glued configuration

Let $G_{\mathrm{in}}$ and $G_{\mathrm{out}}$ be simple graphs on finite sets $V_{\mathrm{in}}$ and $V_{\mathrm{out}}$, and $\iota : V_{\mathrm{in}} \to V_{\mathrm{out}}$ an injective map that [matches adjacency](ocd-adj-match.md) ($x \sim y$ in $G_{\mathrm{in}}$ if and only if $\iota x \sim \iota y$ in $G_{\mathrm{out}}$), and let $p \in \mathbb{R}$. Configurations on $V$ are assignments of open/closed states to all unordered pairs of elements of $V$ (loops included); $\iota$ maps a pair $\{x, y\}$ to $\{\iota x, \iota y\}$, and the images of pairs of $V_{\mathrm{in}}$ are the [inner pairs](ocd-inner-edge-finset.md). For all configurations $\psi$ on $V_{\mathrm{out}}$ and $\omega$ on $V_{\mathrm{in}}$,

$$\pi_{G_{\mathrm{out}}}(\psi \oplus \omega) = \pi_{G_{\mathrm{in}}}(\omega)\, \pi^{\mathrm{out}}(\psi),$$

where $\pi_G(\eta) = \prod_{e \in E(G)} (p \text{ if } e \text{ is open in } \eta,\ 1 - p \text{ otherwise})$ is the [Bernoulli edge product](../../random-cluster-measures-on-finite-graphs/edge-product.md), $\psi \oplus \omega$ is the [glued configuration](ocd-psi-ext.md) (inner pairs take their state from $\omega$, other pairs from $\psi$), and $\pi^{\mathrm{out}}(\psi)$ is the [outer edge factor](ocd-psi-edge-factor.md).
