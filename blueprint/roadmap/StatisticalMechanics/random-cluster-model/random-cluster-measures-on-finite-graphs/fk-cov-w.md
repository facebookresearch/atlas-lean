# Covariance under the inhomogeneous random-cluster measure

Let $G = (V, E)$ be a simple graph on a finite set $V$, let $p_e \in \mathbb{R}$ be edge parameters indexed by the unordered pairs $e$ of elements of $V$, let $q \in \mathbb{R}$, and let $f, g$ be real functions of configurations (assignments of open/closed states to all unordered pairs of elements of $V$). The weighted covariance is

$$\mathrm{Cov}_{\mathbf p}(f, g) = \langle fg \rangle_{\mathbf p} - \langle f \rangle_{\mathbf p}\, \langle g \rangle_{\mathbf p}, \qquad \langle h \rangle_{\mathbf p} = \sum_\omega h(\omega)\, \phi^{\mathbf p}_{G,q}(\omega),$$

where $\phi^{\mathbf p}_{G,q}(\omega) = w^{\mathbf p}_{G,q}(\omega)/Z^{\mathbf p}_{G,q}$ is the [inhomogeneous random-cluster probability](fk-prob-w.md): the [inhomogeneous weight](fk-weight-w.md) divided by the [partition function](fk-zw.md), read as $0$ when $Z^{\mathbf p}_{G,q} = 0$. When $0 \le p_e \le 1$ for every $e$ and $q > 0$, the weights are nonnegative with positive total, $\phi^{\mathbf p}_{G,q}$ is a probability distribution on configurations, $\langle \cdot \rangle_{\mathbf p}$ is its [expectation](fk-mean-w.md), and $\mathrm{Cov}_{\mathbf p}$ is the usual covariance. For other real parameters the expression above is a normalized weighted sum and need not be a covariance in the probabilistic sense.
