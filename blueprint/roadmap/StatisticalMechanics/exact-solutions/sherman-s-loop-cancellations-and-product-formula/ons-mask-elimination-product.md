# Product of first-return factors along a dart elimination

Let $L \ge 1$, $x \in \mathbb{R}$, $a, b \in \{0, 1\}$, $\mathcal{F}$ a finite set of darts of the torus $T_L = (\mathbb{Z}/L\mathbb{Z})^2$, and $(e_1, \dots, e_k)$ a list of darts. The elimination product is defined recursively: it is $1$ for the empty list, and for $(e_1, e_2, \dots, e_k)$ it is

$$\Big(1 - \sum_{s} f\big(K_{a,b}^{\mathcal F}; e_1, \bar e_1; s\big)\Big) \cdot \Pi\big(\mathcal{F} \cup \{e_1, \bar e_1\};\ (e_2, \dots, e_k)\big),$$

where the series runs over all lists $s$ of darts (a non-summable series counting as $0$), $f(\Lambda; e, r; s)$ is the [first-return weight](ons-first-return-weight.md), $\bar e$ is the reverse of $e$, $K_{a,b}$ is the [twisted Kac–Ward matrix](../kac-ward-matrices/ons-kwmat-phase.md) of the torus $T_L = (\mathbb{Z}/L\mathbb{Z})^2$ with parameters $x$, $\omega = e^{i\pi/4}$, $u = e^{i\pi a/L}$, $v = e^{i\pi b/L}$, and $K_{a,b}^{\mathcal F}$ denotes $K_{a,b}$ with every row and column indexed by a dart of $\mathcal{F}$ set to $0$.
