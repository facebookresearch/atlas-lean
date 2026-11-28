# Sensitivity and equicontinuity of cellular automata

An equicontinuous point of a cellular automaton is a configuration whose nearby configurations stay close to it forever; sensitivity to initial conditions requires instead that every configuration have arbitrarily close configurations whose orbits eventually separate.

Let $(S^{\mathbb{Z}^d}, G)$ be a [cellular automaton on $\mathbb{Z}^d$](../cellular-automata-on-z-d.md), given by its finite state set, neighborhood and local rule, with the configuration space carrying the metric $d(x, y) = 2^{-\min\{\|i\|_\infty : x_i \ne y_i\}}$ of the product topology. A configuration $x$ is an *equicontinuous point* of $G$ if for every $\varepsilon > 0$ there is $\delta > 0$ such that $d(G^n(x), G^n(y)) < \varepsilon$ for all $n \in \mathbb{N}$ and all $y$ with $d(x, y) < \delta$. The automaton is *sensitive to initial conditions* if there is $\varepsilon > 0$ such that for every $\delta > 0$ and every configuration $x$ some $y$ with $d(x, y) < \delta$ and some $n$ satisfy $d(G^n(x), G^n(y)) > \varepsilon$. Let $\mathcal{E}_{qu}$ be the set of $d$-dimensional cellular automata having an equicontinuous point, $\mathcal{S}_{ens}$ the set of sensitive ones, and $\mathcal{N}$ the set of those that are neither; the three sets partition all cellular automata of dimension $d$.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](../cellular-automata-on-z-d.md)

## Proof depends on

None.

## Expansion

An automaton with an equicontinuous point is never sensitive, so the three classes are disjoint and cover all automata; in dimension one Kůrka showed that every automaton is either sensitive or has equicontinuous points, so the third class is empty there.

## Sources

- M. Sablik and G. Theyssier, "Topological dynamics of cellular automata: dimension matters", *Theory of Computing Systems* 48(3):693–714, 2011 (published online 2010), doi:10.1007/s00224-010-9255-x; read in arXiv:0811.2731v2: the definitions of Section 2 (Definitions) and the introduction (Kůrka's dichotomy in dimension one).
