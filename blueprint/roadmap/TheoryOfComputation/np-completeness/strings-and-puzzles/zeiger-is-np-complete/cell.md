# Cell content in a ZEIGER grid

For a ZEIGER instance $I$ and a position $(r, c)$ with $0 \le r < \mathrm{rows}(I)$ and $0 \le c < \mathrm{cols}(I)$, the cell content $\mathrm{cell}_I(r, c) \in \mathbb{N} \times \mathbb{N}$ is the pair $(d, a)$ stored as entry $c$ of row $r$. If row $r$ is shorter than $c + 1$ entries, the content defaults to $(0, 0)$.
