# Pointwise limits of convex maps are convex with one-sided derivatives

Let $(g_i)_{i \in I}$ be a family of convex functions $\mathbb{R} \to \mathbb{R}$, let $\mathcal{F}$ be a proper filter on $I$ (for instance $i \to \infty$ along $\mathbb{N}$), and let $g : \mathbb{R} \to \mathbb{R}$ satisfy $g_i(x) \to g(x)$ along $\mathcal{F}$ for every $x \in \mathbb{R}$. Write $\mathrm{sl}_h(a, b) = (h(b) - h(a))/(b - a)$ for the slope of a function $h$, read as $0$ when $a = b$, and let $g'_+$ and $g'_-$ be the [right](pressure-right-deriv.md) and [left derivatives](pressure-left-deriv.md) of $g$ (each read as $0$ where the one-sided limit does not exist). Then:

- $g$ is convex on $\mathbb{R}$;
- for every $t$, the right derivative of $g$ at $t$ exists and equals $g'_+(t)$, and the left derivative exists and equals $g'_-(t)$; equivalently $\mathrm{sl}_g(t, s) \to g'_+(t)$ as $s \downarrow t$ and $\mathrm{sl}_g(t, s) \to g'_-(t)$ as $s \uparrow t$;
- for all $a, b \in \mathbb{R}$, $\mathrm{sl}_{g_i}(a, b) \to \mathrm{sl}_g(a, b)$ along $\mathcal{F}$;
- $g'_-(t) \le g'_+(t)$ for every $t$, the functions $g'_+$ and $g'_-$ are nondecreasing, and the set $\{t : g'_-(t) \ne g'_+(t)\}$ is countable.
