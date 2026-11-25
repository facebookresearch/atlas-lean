# Walk-series square root of $\det(1 - \Lambda)$

For a finite set $E$ and a matrix $\Lambda \in \mathbb{C}^{E \times E}$, the walk-series root is

$$\exp\Big(-\frac{1}{2} \sum_{n=0}^{\infty} \frac{1}{n + 1} \sum_{v_0, \dots, v_n \in E} \prod_{k=0}^{n} \Lambda(v_k, v_{k+1})\Big),$$

with indices mod $n + 1$ (so the inner sum is $\operatorname{tr}(\Lambda^{n+1})$), where a series that is not summable is assigned the value $0$. When the series converges absolutely this equals a square root of $\det(1 - \Lambda)$.
