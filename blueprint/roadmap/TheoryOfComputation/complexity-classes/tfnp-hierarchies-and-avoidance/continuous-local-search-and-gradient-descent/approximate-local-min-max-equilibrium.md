# Approximate local min-max equilibria of constrained smooth objectives and the trivial, local and global regimes

Let $f:[0,1]^{d_1}\times[0,1]^{d_2}\to\mathbb{R}$ be $G$-Lipschitz and $L$-smooth (gradient $L$-Lipschitz) and let a polytope be given by linear constraints $g(x,y)\le0$. For $\varepsilon,\delta>0$ a feasible point $(x^*,y^*)$ is an **$(\varepsilon,\delta)$-local min-max equilibrium** if

$$
f(x^*,y^*)<f(x,y^*)+\varepsilon\ \ \text{for all feasible }(x,y^*)\text{ with }\|x-x^*\|\le\delta,
$$

$$
f(x^*,y^*)>f(x^*,y)-\varepsilon\ \ \text{for all feasible }(x^*,y)\text{ with }\|y-y^*\|\le\delta .
$$

Regimes: **trivial** if $\delta<\varepsilon/G$ (every feasible point qualifies); **local** if $\delta<\sqrt{2\varepsilon/L}$, where such equilibria always exist and are computationally equivalent to approximate fixed points of the projected gradient descent-ascent map $(x,y)\mapsto(\Pi(x-\nabla_xf),\Pi(y+\nabla_yf))$; **global** if $\delta$ is comparable to the diameter of the feasible set, where existence is not guaranteed.

## Depends on

- [Karush–Kuhn–Tucker conditions for inequality constraints](../../../../Analysis/convex-analysis-and-variations/karush-kuhn-tucker-inequality.md)

## Sources

- Constantinos Daskalakis, Stratis Skoulakis and Manolis Zampetakis, "The Complexity of Constrained Min-Max Optimization", STOC (2021), arXiv:2009.09623.
