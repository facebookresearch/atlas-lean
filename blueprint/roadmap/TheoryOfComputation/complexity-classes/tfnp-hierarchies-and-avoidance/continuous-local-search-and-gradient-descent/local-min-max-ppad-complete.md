# Daskalakis–Skoulakis–Zampetakis: local min-max equilibria of smooth objectives are PPAD-complete in the local regime

In the white-box model (objective and gradient given by circuits): (i) computing an $(\varepsilon,\delta)$-local min-max equilibrium in the local regime is PPAD-complete, and hardness holds already when the feasible set is a polytope contained in $[0,1]^d$, $f$ takes values in $[-1,1]$, and $G$, $L$, $1/\varepsilon$, $1/\delta$ are polynomial in $d$; (ii) equivalently, computing $\alpha$-approximate fixed points of projected gradient descent-ascent is PPAD-complete with $1/\alpha$, $G$, $L$ polynomial in $d$; (iii) in the global regime, deciding whether an approximate local min-max point exists is NP-hard even for constant $\varepsilon$. In the black-box oracle model, every algorithm for the local regime needs a number of queries exponential in at least one of $1/\varepsilon$, $L$, $G$, $d$, and exponential in $d$ even when the others are polynomial in $d$. By contrast, approximate local minima of smooth objectives with range $[-B,B]$ are found with $O(BL/\varepsilon)$ gradient steps.

## Proof sketch

Membership: projected gradient descent-ascent with the joint Euclidean projection of $(x-\nabla_xf,\,y+\nabla_yf)$ onto the feasible polytope $K$ is a Lipschitz self-map of $K$ (the two coordinate-slice projections need not map $K$ into itself), so Brouwer guarantees fixed points and a bound on its Lipschitz constant places their approximation in PPAD. Its fixed points satisfy the coordinate-slice first-order conditions, approximate fixed points of the joint and coordinate-slice maps are computationally equivalent, and these approximate fixed points are local min-max equilibria in the local regime by smoothness. Hardness goes through a new PPAD-hard discrete problem BISPERNER (a $d$-cube simplicization coloured with $2d$ colours, each vertex receiving $d$ colours, seeking a vertex whose neighbourhood sees all colours), a discrete constrained zero-sum game whose local equilibria encode BISPERNER solutions, and an efficient smooth interpolation of that game to the continuum, which in high dimension is the main technical step and also yields the oracle lower bound.

## Depends on

- [Approximate local min-max equilibria of constrained smooth objectives and the trivial, local and global regimes](approximate-local-min-max-equilibrium.md)

## Sources

- Constantinos Daskalakis, Stratis Skoulakis and Manolis Zampetakis, "The Complexity of Constrained Min-Max Optimization", STOC (2021), arXiv:2009.09623.
