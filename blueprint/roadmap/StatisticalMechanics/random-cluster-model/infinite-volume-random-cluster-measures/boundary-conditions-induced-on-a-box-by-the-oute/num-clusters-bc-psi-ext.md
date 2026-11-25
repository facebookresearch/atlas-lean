# Wired cluster count of a glued configuration splits additively

Let $d, n \in \mathbb{N}$, let $\Lambda_m = \{-m, \dots, m\}^d$ carry its nearest-neighbour edges (so $\Lambda_n \subseteq \Lambda_{n+1}$), and let $\psi$ be an assignment of open/closed states to the unordered pairs of vertices of $\Lambda_{n+1}$ (the outer configuration), and $\omega$ one for the unordered pairs of vertices of $\Lambda_n$. Then

$$k^{K}_{\Lambda_{n+1}}(\psi \oplus \omega) = k^{W_\psi}_{\Lambda_n}(\omega) + N_{\mathrm{out}}(\psi),$$

where $k^C_G(\eta)$ is the [number of clusters under the wiring $C$](../../fkg-inequality-and-monotonicity-of-random-cluste/num-clusters-bc.md) (components of the graph formed by the edges of $G$ open in $\eta$ and the edges of $C$), $K$ is the clique on $\partial\Lambda_{n+1}$, $\psi \oplus \omega$ is the [glued configuration](psi-ext.md) (the pairs with both endpoints in $\Lambda_n$ take their state from $\omega$, all other pairs from $\psi$), $W_\psi$ is the [induced wiring](induced-wiring.md) on $\Lambda_n$ (distinct vertices of $\Lambda_n$ joined by a path in the outer graph $O_\psi$), and $N_{\mathrm{out}}(\psi)$ is the [number of components of the outer graph containing no vertex of $\Lambda_n$](outside-shift.md).
