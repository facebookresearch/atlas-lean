# Right derivative of the pressure

For an arbitrary function $g : \mathbb{R} \to \mathbb{R}$ and $x \in \mathbb{R}$, the right derivative $g'_+(x)$ is the real number

$$g'_+(x) = \lim_{h \downarrow 0} \frac{g(x + h) - g(x)}{h}$$

when this one-sided limit exists and is finite (that is, when $g$ is differentiable at $x$ within $(x, \infty)$), and $g'_+(x) = 0$ otherwise. Thus $g \mapsto g'_+$ is defined for every real function: for example, for $g(x) = \sqrt{|x|}$ the right difference quotients at $0$ tend to $+\infty$, so $g'_+(0) = 0$. For convex $g$ the one-sided limit always exists, and $g'_+(x)$ is then the genuine right derivative.
