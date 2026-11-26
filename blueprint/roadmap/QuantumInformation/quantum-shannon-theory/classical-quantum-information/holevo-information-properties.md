# Holevo information as classical-quantum mutual information and its bounds

For a finite ensemble $(p,\rho)$ on $\mathbb{C}^\iota$ with classical-quantum state $\rho_{QX}$:

1. $I(Q:X)_\rho = (\ln 2)\,\chi(p,\rho)$ (nats versus bits);
2. $0 \le \chi(p,\rho) \le \min\big\{H(p),\ S(\textstyle\sum_x p(x)\rho_x),\ \log_2|\iota|\big\}$, where $H(p)$ is the Shannon entropy in bits. In particular von Neumann entropy is concave.

## Proof sketch

By the classical-quantum mutual information formula, $I(Q:X) = \sum_x p(x)D(\rho_x\|\bar\rho)$, and expanding the traces gives $(\ln 2)(S(\bar\rho) - \sum_x p(x)S(\rho_x))$. Nonnegativity is nonnegativity of relative entropy; the bound by $S(\bar\rho)$ and $\log_2|\iota|$ uses $S\ge 0$ and $S\le\log_2 d$. For the bound by $H(p)$, $p(x)\rho_x\le\bar\rho$ gives $D(\rho_x\|\bar\rho)\le-\ln p(x)$ by reference domination, and averaging over $p$ gives $(\ln 2)\chi \le (\ln 2) H(p)$.

## Depends on

- [Von Neumann entropy and Holevo information](von-neumann-entropy-and-holevo-information.md)
- [Classical-quantum states](classical-quantum-state.md)
- [Quantum mutual information](quantum-mutual-information.md)

## Proof depends on

- [Mutual information of a classical-quantum state](classical-quantum-mutual-information.md)
- [Nonnegativity of quantum relative entropy for singular states (Klein's inequality)](../../quantum-states-distances-and-entropy/quantum-relative-entropy/relative-entropy-nonnegativity.md)
- [Basic properties of von Neumann entropy: bounds, additivity, subadditivity and Araki-Lieb](von-neumann-entropy-properties.md)
- [Relative entropy under domination of the reference](../../quantum-states-distances-and-entropy/quantum-relative-entropy/relative-entropy-reference-domination.md)

## Sources

- A. S. Holevo, "Bounds for the quantity of information transmitted by a quantum communication channel", Problems of Information Transmission 9:177-183, 1973.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
