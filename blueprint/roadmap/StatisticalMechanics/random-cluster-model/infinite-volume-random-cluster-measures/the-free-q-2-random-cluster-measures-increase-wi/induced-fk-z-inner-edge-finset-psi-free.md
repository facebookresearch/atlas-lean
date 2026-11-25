# Conditional partition function in terms of the induced wiring

Let $d, n \in \mathbb{N}$, $\Lambda_m = \{-m, \dots, m\}^d$ (so $\Lambda_n \subseteq \Lambda_{n+1}$), and let $\psi$ be a configuration of $\Lambda_{n+1}$ (an assignment of open/closed states to the unordered pairs of vertices of $\Lambda_{n+1}$), and let $p, q \in \mathbb{R}$. Let $F$ be the set of unordered pairs of vertices of $\Lambda_{n+1}$ with both elements in $\Lambda_n$. Then

$$\sum_{\rho \in \mathcal{F}_\psi} w_{\Lambda_{n+1}}(\rho) = Z^{W^0_\psi}_{\Lambda_n}(p, q)\, s^0(\psi),$$

where $\mathcal{F}_\psi$ is the set of configurations of $\Lambda_{n+1}$ agreeing with $\psi$ off $F$, $w_G$ is the [random-cluster weight](../../random-cluster-measures-on-finite-graphs/fk-weight.md), $Z^C_G$ the [partition function with boundary wiring $C$](../../fkg-inequality-and-monotonicity-of-random-cluste/bc-z.md), $W^0_\psi$ is the [free induced wiring](induced-wiring-free.md) on $\Lambda_n$ (distinct $x, y \in \Lambda_n$ joined by a path in the outer open graph $O^0_\psi$), and $s^0(\psi)$ is the [outer weight factor](psi-shift-free.md).
