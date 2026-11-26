# The low individual degree test

Let $\mathbb{F}$ be a finite field, $m \ge 1$, and $d \ge 0$. A polynomial $g : \mathbb{F}^m \to \mathbb{F}$ has *individual degree* at most $d$ if it has degree at most $d$ in each variable separately. The two-player *low individual degree test* sends one player a uniformly random point $u \in \mathbb{F}^m$ (asking for $g(u)$) and the other an axis-parallel line, a diagonal line (up to a cutoff), or a point, asking for the restriction of $g$ to that line as a univariate polynomial of degree at most $d$ (respectively $md$ for diagonal lines); it accepts if the answers are consistent at the shared point. Honest players answering with a polynomial of individual degree at most $d$ win with probability $1$.

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum Soundness of the Classical Low Individual Degree Test", arXiv:2009.12982, 2020.
- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "MIP* = RE", arXiv:2001.04383, 2020.
