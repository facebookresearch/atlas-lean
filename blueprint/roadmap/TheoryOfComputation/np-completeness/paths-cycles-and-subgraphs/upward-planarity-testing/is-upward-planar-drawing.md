# Planar straight-line upward drawings

Let $G$ be a digraph on a vertex type $V$ and $f : V \to \mathbb{R}^2$. Write $[a, b] = \{a + t(b - a) : 0 \le t \le 1\}$ for the closed segment between points $a, b \in \mathbb{R}^2$, and $y(p)$ for the second coordinate of $p$. The map $f$ is a planar straight-line upward drawing of $G$ when all of the following hold:

- $f$ is injective;
- for every arc $u \to v$ of $G$, $y(f(u)) < y(f(v))$;
- for all arcs $u \to v$ and $x \to y$ of $G$ with $\{u, v\} \ne \{x, y\}$,

    $$[f(u), f(v)] \cap [f(x), f(y)] \subseteq \{f(u), f(v)\} \cap \{f(x), f(y)\};$$

- for every arc $u \to v$ of $G$ and every vertex $w$, if $f(w) \in [f(u), f(v)]$ then $w = u$ or $w = v$.
