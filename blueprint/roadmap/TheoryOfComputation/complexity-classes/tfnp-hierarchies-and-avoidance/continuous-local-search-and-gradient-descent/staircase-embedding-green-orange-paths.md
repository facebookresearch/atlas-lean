# Staircase embedding of END-OF-LINE into a planar descent landscape with green descending and orange ascending paths

Given an END-OF-LINE instance on $[2^n]$ and an ITER instance on $[2^m]$, set $N=2^n\cdot2^{m+4}$ and split $[0,N]^2$ into $2^n\times2^n$ big squares $B(v_1,v_2)$; vertex $v$ sits at the centre of the diagonal square $B(v,v)$. Values of $f$ and of the descent direction $-\nabla f$ are prescribed on the grid $\{0,\dots,N\}^2$: off all paths (the *environment*) $f(x,y)=x+y$; a forward edge $(v_1,v_2)$, $v_1<v_2$, becomes a **green path** running right from $B(v_1,v_1)$ to $B(v_2,v_1)$ then up to $B(v_2,v_2)$, along which $f$ decreases and stays below all environment values; a backward edge becomes an **orange path** running left then down, along which $f$ increases and stays above the environment. The green path of the trivial source starts at the origin.

Then, for all sufficiently small (inverse-exponential) $\varepsilon$, every $\varepsilon$-KKT point of the resulting function lies in a square $B(v,v)$ where either $v$ is an END-OF-LINE solution (a sink or a source $v\ne1$), or $v$ has one incoming and one outgoing edge of different colours (green-in/orange-out forces a local minimum, orange-in/green-out a local maximum). Same-colour paths are joined at $B(v,v)$ without creating KKT points, and the trivial source creates none.

## Proof sketch

Away from paths $\nabla f=(1,1)$ points away from the boundary constraints except at the origin, where the outgoing green path removes the minimum. Along a monotone path the prescribed descent direction is tangent to the path and of norm bounded below, so interior points are not stationary; KKT points can only arise where a path starts or ends in the environment or where descending and ascending paths meet. Path ends in the environment correspond exactly to sinks and non-trivial sources, and a green end meeting an orange start (or vice versa) forces an extremum by continuity of $f$ along the joined route.

## Depends on

- [The KKT search problem for smooth objectives on bounded polytopes with Taylor-violation witnesses](kkt-search-problem.md)
- [ITER and the EITHER-SOLUTION combinator for building PPAD ∩ PLS-complete problems](iter-and-either-solution.md)
- [The END-OF-THE-LINE graph](../../../completeness-other-classes/ppad-and-the-end-of-the-line-problem/adj.md)

## Sources

- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
- Pavel Hubáček and Eylon Yogev, "Hardness of Continuous Local Search: Query Complexity and Cryptographic Lower Bounds", SODA (2017) and SIAM Journal on Computing (2020), ECCC TR16-063.
