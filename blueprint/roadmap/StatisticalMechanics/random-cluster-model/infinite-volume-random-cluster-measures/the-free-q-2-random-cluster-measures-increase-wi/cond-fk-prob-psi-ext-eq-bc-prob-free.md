# Domain Markov property for the free measure on nested boxes

Let $d, n \in \mathbb{N}$, $0 < p < 1$ and $q > 0$, let $\Lambda_m = \{-m, \dots, m\}^d$, and let $F$ be the set of unordered pairs of vertices of $\Lambda_{n+1}$ with both elements in $\Lambda_n$. For configurations $\psi$ of $\Lambda_{n+1}$ and $\omega$ of $\Lambda_n$,

$$\phi(\psi \oplus \omega \mid F, \psi) = \phi^{W^0_\psi}_{\Lambda_n,p,q}(\omega),$$

where $\phi(\cdot \mid F, \psi)$ is the [conditional free random-cluster probability](../../random-cluster-measures-on-finite-graphs/cond-fk-prob.md) on $\Lambda_{n+1}$ given agreement with $\psi$ off $F$, $\psi \oplus \omega$ is the [glued configuration](../boundary-conditions-induced-on-a-box-by-the-oute/psi-ext.md), $W^0_\psi$ is the free induced wiring on $\Lambda_n$ (distinct $x, y \in \Lambda_n$ joined by a path of edges of $\Lambda_{n+1}$ open in $\psi$ that do not have both endpoints in $\Lambda_n$), and $\phi^C_{\Lambda_n,p,q}$ is the [random-cluster probability with boundary wiring $C$](../../fkg-inequality-and-monotonicity-of-random-cluste/bc-prob.md).
