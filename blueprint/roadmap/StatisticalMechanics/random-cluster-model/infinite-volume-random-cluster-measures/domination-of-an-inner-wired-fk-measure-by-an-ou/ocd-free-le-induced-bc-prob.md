# Free inner measure is dominated by every induced-wiring measure

Let $G_{\mathrm{in}}$ and $G_{\mathrm{out}}$ be simple graphs on finite sets $V_{\mathrm{in}}$ and $V_{\mathrm{out}}$, and $\iota : V_{\mathrm{in}} \to V_{\mathrm{out}}$ an injective map that [matches adjacency](ocd-adj-match.md) ($x \sim y$ in $G_{\mathrm{in}}$ if and only if $\iota x \sim \iota y$ in $G_{\mathrm{out}}$), and let $\partial_{\mathrm{out}} \subseteq V_{\mathrm{out}}$ be a set of boundary vertices, let $0 < p < 1$ and $q \ge 1$, and let $\psi$ be a configuration on $V_{\mathrm{out}}$. For every increasing set $A$ of configurations on $V_{\mathrm{in}}$,

$$\phi_{G_{\mathrm{in}}}(A) \le \phi^{W_\psi}_{G_{\mathrm{in}}}(A),$$

where $\phi_{G_{\mathrm{in}}}$ is the (free) [random-cluster probability](../../random-cluster-measures-on-finite-graphs/fk-prob.md) on $G_{\mathrm{in}}$, $W_\psi$ is the [induced wiring](ocd-induced-wiring.md) on $V_{\mathrm{in}}$ (distinct $x, y$ with $\iota x$ and $\iota y$ joined by a path in $O_\psi$), and $\phi^{W_\psi}_{G_{\mathrm{in}}}$ is the [random-cluster probability](../../fkg-inequality-and-monotonicity-of-random-cluste/bc-prob.md) on $G_{\mathrm{in}}$ with boundary wiring $W_\psi$. For a function $\mu$ on configurations and a set $A$, $\mu(A) = \sum_{\omega \in A} \mu(\omega)$.
