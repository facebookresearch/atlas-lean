# Cerf's theorem $\Gamma_4 = 0$

Let $S^3 \subset \mathbb{R}^4$ be the unit sphere. Every
smooth diffeomorphism $f$ of $S^3$ is smoothly isotopic to the restriction of a linear isometry of
$\mathbb{R}^4$: there are an orthogonal matrix $A \in O(4)$ and smooth maps
$F, F' : [0, 1] \times S^3 \to S^3$ such that for every $t \in [0, 1]$ the maps $F(t, \cdot)$ and
$F'(t, \cdot)$ are inverse to each other, and $F(0, p) = f(p)$ and $F(1, p) = Ap$ for all
$p \in S^3$.

## Sources

- J. Cerf, Sur les diffeomorphismes de la sphere de dimension trois, Lecture Notes in Mathematics 53, Springer (1968). Via leanprover/lean-eval@38361be, problem `cerf_gamma_four`.
