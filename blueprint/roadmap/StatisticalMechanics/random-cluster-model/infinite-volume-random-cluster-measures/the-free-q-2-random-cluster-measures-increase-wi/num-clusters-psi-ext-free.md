# Cluster count of a glued configuration splits additively

Let $d, n \in \mathbb{N}$, $\Lambda_m = \{-m, \dots, m\}^d$ (so $\Lambda_n \subseteq \Lambda_{n+1}$), and let $\psi$ be a configuration of $\Lambda_{n+1}$ (an assignment of open/closed states to the unordered pairs of vertices of $\Lambda_{n+1}$) and $\omega$ a configuration of $\Lambda_n$. Then

$$k_{\Lambda_{n+1}}(\psi \oplus \omega) = k^{W^0_\psi}_{\Lambda_n}(\omega) + N^0_{\mathrm{out}}(\psi),$$

where $k_G$ is the [number of open clusters](../../random-cluster-measures-on-finite-graphs/num-clusters.md), $k^C_G$ the [number of clusters under the wiring $C$](../../fkg-inequality-and-monotonicity-of-random-cluste/num-clusters-bc.md), $\psi \oplus \omega$ is the [glued configuration](../boundary-conditions-induced-on-a-box-by-the-oute/psi-ext.md) (pairs with both elements in $\Lambda_n$ take their state from $\omega$, the others from $\psi$), $W^0_\psi$ is the [free induced wiring](induced-wiring-free.md) on $\Lambda_n$ (distinct $x, y \in \Lambda_n$ joined by a path in the outer open graph $O^0_\psi$), and $N^0_{\mathrm{out}}(\psi)$ is the [number of avoiding outer components](outside-shift-free.md).
