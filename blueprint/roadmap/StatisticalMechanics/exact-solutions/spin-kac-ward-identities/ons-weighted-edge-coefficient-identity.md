# Edge coefficient identity on the $L \times L$ torus

For $L > 2$, the edge coefficient identity holds when for all $a, b \in \{0, 1\}$, every weight $w$ on unordered pairs of sites and every $q$ with $0 \le q < 1/(2N^2)$ with $N = 4L^2$ the number of darts, and $|w(f)| \le q$ for every pair $f$, and every dart $e = (p, \mu)$,

$$C_w(\{p, p + s(\mu)\}) = -R\big(K^{\{e, \bar e\}}\big) \cdot \sum_s f(K; e, \bar e; s),$$

where $C_w(f) = \sum_{F \ni f} \chi_{a,b}([F]) \prod_{g \in F} w(g)$ is the [weighted edge coefficient](ons-weighted-spin-edge-coefficient.md) (over even subgraphs $F$ of $T_L$ containing $f$), $K = K^w_{a,b}$ is the [edge-weighted twisted Kac–Ward matrix](../kac-ward-matrices/ons-kwmat-weighted-phase.md) with weights $w$, turning phase $\omega = e^{i\pi/4}$ and boundary phases $e^{i\pi a/L}, e^{i\pi b/L}$, $K^{\{e, \bar e\}}$ is $K$ with the rows and columns of $e$ and $\bar e$ set to $0$, $R(\Lambda) = \exp\big(-\tfrac12 \sum_{n \ge 0} \operatorname{tr}(\Lambda^{n+1})/(n+1)\big)$ is the [walk-series root](../kac-ward-matrices/ons-det-walk-root.md) (a non-summable series counting as $0$), and $f(\Lambda; e, \bar e; s)$ is the [first-return weight](../sherman-s-loop-cancellations-and-product-formula/ons-first-return-weight.md) of a list $s$ of darts and the series over $s$ runs over all lists (a non-summable series counting as $0$).
