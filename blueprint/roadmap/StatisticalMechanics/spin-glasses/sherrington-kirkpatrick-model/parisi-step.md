# One step of the Parisi recursion

Given a function $f \colon \mathbb{R} \to \mathbb{R}$, a variance $v \in \mathbb{R}$ and a parameter
$m \in \mathbb{R}$, one Parisi step returns

$$y \mapsto \frac1m\log\mathbb{E}\exp\big(m f(y + z)\big), \quad z \sim N(0, v^+),$$

for $m \ne 0$, and $y \mapsto \mathbb{E} f(y + z)$ for $m = 0$ (Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), (1.10), written on
functions of the partial sum $h + \sum_{p < \ell} z_p$). For $v \ge 0$ and $f$ with finite
expectations this is the usual probabilistic formula. For other inputs the step is extended by the
conventions $v^+ = \max(v, 0)$ (a negative variance gives $z = 0$), expectations of non-integrable
functions taken to be $0$, and $\log 0 = 0$.
