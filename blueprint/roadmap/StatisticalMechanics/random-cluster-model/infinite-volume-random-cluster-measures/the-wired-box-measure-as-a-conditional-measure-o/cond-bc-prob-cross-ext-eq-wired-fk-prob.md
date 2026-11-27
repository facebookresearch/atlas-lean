# Domain Markov property for the wired box measure

Let $d, n \in \mathbb{N}$, $0 < p < 1$, $q > 0$, $\Lambda_m = \{-m, \dots, m\}^d$, and let $F$ be the set of unordered pairs of vertices of $\Lambda_{n+1}$ with both elements in $\Lambda_n$. For every configuration $\omega$ of $\Lambda_n$,

$$\phi^{K}_{\Lambda_{n+1},p,q}(\tilde\omega \mid F, \mathbf{0}) = \phi^w_{\Lambda_n,\partial\Lambda_n,p,q}(\omega),$$

where $K$ is the clique on the vertices of $\Lambda_{n+1}$ lying in $\partial\Lambda_n = \Lambda_n \setminus \Lambda_{n-1}$, the left side is the [conditional measure](../../fkg-inequality-and-monotonicity-of-random-cluste/cond-bc-prob.md) of the random-cluster measure on $\Lambda_{n+1}$ with boundary wiring $K$ given agreement with the all-closed configuration $\mathbf{0}$ off $F$, $\tilde\omega$ is the [closed-annulus extension](cross-ext.md) of $\omega$ (equal to $\omega$ on pairs with both elements in $\Lambda_n$ and closed on all other pairs of vertices of $\Lambda_{n+1}$), and $\phi^w_{\Lambda_n,\partial\Lambda_n,p,q}$ is the [wired random-cluster probability](../finite-and-infinite-volume-fk-measures-on-d/wired-fk-prob.md) of $\Lambda_n$ with boundary $\partial\Lambda_n$.

This is a case of the domain Markov property of random-cluster measures (G. Grimmett, *The Random-Cluster Model*, Springer, 2006, Lemma 4.13).
