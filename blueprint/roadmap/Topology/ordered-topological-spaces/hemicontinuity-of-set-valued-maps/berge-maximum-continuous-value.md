# Berge's maximum theorem: continuity of the value function

Let $X$ and $Y$ be topological spaces (no separation axioms assumed), let $f : X \times Y \to \mathbb{R}$ be continuous, and let $\varphi$ assign to each $x \in X$ a nonempty compact set $\varphi(x) \subseteq Y$. Assume $\varphi$ is upper hemicontinuous (whenever $U$ is a neighbourhood of the set $\varphi(x)$, it is a neighbourhood of $\varphi(x')$ for all $x'$ near $x$) and lower hemicontinuous (whenever an open set meets $\varphi(x)$, it meets $\varphi(x')$ for all $x'$ near $x$). Then the value function

$$v(x) = \sup\{ f(x,y) : y \in \varphi(x) \}$$

is continuous on $X$. When $\varphi$ is constant this is the continuity of $x \mapsto \sup_{y \in K} f(x,y)$ for a fixed nonempty compact $K$.

## Sources

- C. Berge, *Topological Spaces* (1963), Chapter VI, §3, Maximum Theorem; C. D. Aliprantis and K. C. Border, *Infinite Dimensional Analysis*, 3rd ed. (2006), Theorem 17.31.
