# Outer wired fibre masses sum to one

Let $G_{\mathrm{in}}$ and $G_{\mathrm{out}}$ be simple graphs on finite sets $V_{\mathrm{in}}$ and $V_{\mathrm{out}}$, and $\iota : V_{\mathrm{in}} \to V_{\mathrm{out}}$ an injective map, and let $\partial_{\mathrm{out}} \subseteq V_{\mathrm{out}}$ be a set of boundary vertices, and let $0 < p < 1$ and $q > 0$. Configurations on $V$ are assignments of open/closed states to all unordered pairs of elements of $V$ (loops included); $\iota$ maps a pair $\{x, y\}$ to $\{\iota x, \iota y\}$, and the images of pairs of $V_{\mathrm{in}}$ are the [inner pairs](ocd-inner-edge-finset.md). Then

$$\sum_{\psi} \phi^K_{G_{\mathrm{out}}}(\mathcal{F}_\psi) = 1,$$

where the sum runs over the configurations $\psi$ on $V_{\mathrm{out}}$ that are closed on every inner pair, $\mathcal{F}_\psi$ is the set of configurations agreeing with $\psi$ off the inner pairs, and $\phi^{K}_{G_{\mathrm{out}}}$ is the random-cluster probability on $G_{\mathrm{out}}$ with boundary wiring the clique $K$ on $\partial_{\mathrm{out}}$ (the wired measure; see [random-cluster probability with a boundary wiring](../../fkg-inequality-and-monotonicity-of-random-cluste/bc-prob.md)).
