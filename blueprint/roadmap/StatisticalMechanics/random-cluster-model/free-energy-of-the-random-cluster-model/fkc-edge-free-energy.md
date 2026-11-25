# Edge-normalized box free energy of the random-cluster model

For $d, n \in \mathbb{N}$ and $s, q \in \mathbb{R}$, the edge-normalized free energy of the box $\Lambda_n = \{-n, \dots, n\}^d$ is

$$\frac{\log Z^E_{\Lambda_n}(\sigma(s), q)}{|E_n|} + \log(1 + e^s),$$

where $\sigma(s) = e^s/(1 + e^s)$, $|E_n|$ is the number of edges of $\Lambda_n$, $Z^E_G(p, q)$ is the [edge partition function](../per-box-agreement-of-free-and-wired-random-clust/ecz-fk-zedge.md) $Z^E_G(p, q) = \sum_\omega p^{o(\omega)}(1 - p)^{c(\omega)} q^{k(\omega)}$, the sum over the configurations $\omega$ that are closed on every unordered pair of vertices that is not an edge of $G$ ($o, c$ count open and closed edges, $k$ the open clusters), the quotient is read as $0$ when $|E_n| = 0$, and $\log x$ means $\log |x|$ for $x \ne 0$ with $\log 0 = 0$.
