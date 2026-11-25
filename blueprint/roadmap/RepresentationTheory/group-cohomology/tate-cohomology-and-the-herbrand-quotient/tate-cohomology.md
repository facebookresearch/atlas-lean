# Tate cohomology groups of a finite group

Let $G$ be a finite group, $R$ a commutative ring and $M$ a representation of $G$ on an $R$-module. The Tate complex
of $M$ is the complex indexed by $\mathbb{Z}$ obtained by joining the complex of inhomogeneous chains of $M$, placed in
degrees $\le -1$, to the complex of inhomogeneous cochains, placed in degrees $\ge 0$, by the norm map
$N \colon M \to M$, $m \mapsto \sum_{g \in G} g m$, from the chains of degree $0$ (in degree $-1$) to the cochains of
degree $0$. For $n \in \mathbb{Z}$, the Tate cohomology group $\hat H^n(G, M)$ is the $n$-th cohomology of this
complex, an $R$-module. In particular $\hat H^0(G, M) = M^G / N(M)$ and
$\hat H^{-1}(G, M) = \ker N / I_G M$, where $I_G M$ is spanned by the elements $gm - m$.
