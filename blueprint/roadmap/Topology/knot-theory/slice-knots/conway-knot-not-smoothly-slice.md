# The Conway knot is not smoothly slice (Piccirillo)

Let $K$ be the Conway knot $11n34$,
realized as a closed polyline in $\mathbb{R}^3$. There is no smooth knot $J$, that is, a smooth
$2\pi$-periodic map $\mathbb{R} \to \mathbb{R}^3$ with nowhere vanishing derivative that is
injective on $[0, 2\pi)$, with both of the following properties: some topological ambient isotopy
of $\mathbb{R}^3$ carries the image of $J$ onto the image of $K$; and there is a smooth map
$D \colon \mathbb{R}^2 \to \mathbb{R}^3 \times \mathbb{R}$ that is injective with injective
derivative on the closed unit disk $\overline{\mathbb{D}}$, takes $\overline{\mathbb{D}}$ into the
half-space $\mathbb{R}^3 \times [0, \infty)$, takes a point of $\overline{\mathbb{D}}$ to height
$0$ exactly when it lies on the unit circle, and whose $\mathbb{R}^3$-component maps the unit
circle onto the image of $J$.

## Sources

- https://arxiv.org/abs/1808.02923 Via leanprover/lean-eval@38361be, problem `conway_knot_not_smoothly_slice`.
