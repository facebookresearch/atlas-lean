# Approximate local min-max equilibria of constrained smooth objectives and the trivial, local and global regimes

Let $f:[0,1]^{d_1}\times[0,1]^{d_2}\to\mathbb{R}$ be $G$-Lipschitz and $L$-smooth (gradient $L$-Lipschitz) and let a polytope be given by linear constraints $g(x,y)\le0$. For $\varepsilon,\delta>0$ a feasible point $(x^*,y^*)$ is an **$(\varepsilon,\delta)$-local min-max equilibrium** if

$$
f(x^*,y^*)<f(x,y^*)+\varepsilon\ \ \text{for all feasible }(x,y^*)\text{ with }\|x-x^*\|\le\delta,
$$

$$
f(x^*,y^*)>f(x^*,y)-\varepsilon\ \ \text{for all feasible }(x^*,y)\text{ with }\|y-y^*\|\le\delta .
$$

Regimes: **trivial** if $\delta<\varepsilon/G$ (every feasible point qualifies); **local** if $\delta<\sqrt{2\varepsilon/L}$, where such equilibria always exist and are computationally equivalent to approximate fixed points of projected gradient descent-ascent; **global** if $\delta$ is comparable to the diameter of the feasible set, where existence is not guaranteed.

Write $K$ for the feasible polytope, $\Pi_K$ for Euclidean projection onto it, and $K(y)=\{x:(x,y)\in K\}$, $K(x)=\{y:(x,y)\in K\}$ for its slices. The coordinate-slice map $(x,y)\mapsto\bigl(\Pi_{K(y)}(x-\nabla_xf(x,y)),\,\Pi_{K(x)}(y+\nabla_yf(x,y))\bigr)$ need not map $K$ into itself: for $K=\{(x,y)\in[0,1]^2:x+y\le1\}$ and $f=-x+y$ it sends $(0,0)$ to $(1,1)\notin K$. The joint map

$$
F(x,y)=\Pi_K\bigl(x-\nabla_xf(x,y),\ y+\nabla_yf(x,y)\bigr)
$$

is a continuous self-map of $K$, so it has fixed points by Brouwer; every fixed point of $F$ satisfies the coordinate-slice conditions $x=\Pi_{K(y)}(x-\nabla_xf(x,y))$ and $y=\Pi_{K(x)}(y+\nabla_yf(x,y))$, and computing approximate fixed points of the two maps is computationally equivalent (Daskalakis–Skoulakis–Zampetakis, Definition 3.8 and the proof of Theorem 5.2).

## Sources

- Constantinos Daskalakis, Stratis Skoulakis and Manolis Zampetakis, "The Complexity of Constrained Min-Max Optimization", STOC (2021), arXiv:2009.09623.
