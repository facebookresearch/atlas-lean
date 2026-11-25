# The Parisi functional

For a function $\xi \colon \mathbb{R} \to \mathbb{R}$ with derivative $\xi'$ (taken to be $0$ at points
where $\xi$ is not differentiable), a field $h \in \mathbb{R}$, an integer $k$ and sequences $m, q$,

$$\mathcal{P}_k(m, q) = \log 2 + X_0 - \frac12\sum_{1 \le \ell \le k} m_\ell\big(\theta(q_{\ell+1}) - \theta(q_\ell)\big),
\qquad \theta(q) = q\,\xi'(q) - \xi(q),$$

where $X_0 = f_0(h)$ comes from the [Parisi recursion](parisi-recursion.md) with variances
$\xi'(q_{\ell+1}) - \xi'(q_\ell)$ (Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), (1.11)–(1.12)). The Parisi constant is
$\mathcal{P}(\xi, h) = \inf \mathcal{P}_k(m, q)$ over all admissible parameters, (1.13).

## Background

- [The Parisi recursion](parisi-recursion.md): the definition of $X_0$.
- [Admissible Parisi parameters](is-parisi-parameter.md): the parameters over which the
  infimum (1.13) runs.
