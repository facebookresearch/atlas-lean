# Random-cluster weight of a glued configuration factorizes

Let $d, n \in \mathbb{N}$, $\Lambda_m = \{-m, \dots, m\}^d$ (so $\Lambda_n \subseteq \Lambda_{n+1}$), and let $\psi$ be a configuration of $\Lambda_{n+1}$ (an assignment of open/closed states to the unordered pairs of vertices of $\Lambda_{n+1}$) and $\omega$ a configuration of $\Lambda_n$, and let $p, q \in \mathbb{R}$. Then

$$w_{\Lambda_{n+1}}(\psi \oplus \omega) = w^{W^0_\psi}_{\Lambda_n}(\omega)\, s^0(\psi),$$

where $w_G$ is the [random-cluster weight](../../random-cluster-measures-on-finite-graphs/fk-weight.md), $w^C_G$ the [weight with boundary wiring $C$](../../fkg-inequality-and-monotonicity-of-random-cluste/bc-weight.md), $\psi \oplus \omega$ is the [glued configuration](../boundary-conditions-induced-on-a-box-by-the-oute/psi-ext.md) (pairs with both elements in $\Lambda_n$ take their state from $\omega$, the others from $\psi$), $W^0_\psi$ is the [free induced wiring](induced-wiring-free.md) on $\Lambda_n$ (distinct $x, y \in \Lambda_n$ joined by a path in the outer open graph $O^0_\psi$), and $s^0(\psi)$ is the [outer weight factor](psi-shift-free.md).
