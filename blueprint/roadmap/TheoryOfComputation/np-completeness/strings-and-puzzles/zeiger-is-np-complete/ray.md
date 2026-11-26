# Cells along an arrow in a ZEIGER grid

For a ZEIGER instance $I$ and positions $x = (r, c)$ and $y = (r', c')$ of the grid, $y$ lies along the arrow of $x$ when $y$ is strictly beyond $x$ in the direction of the arrow of $x$. Writing $d$ for the arrow component of $\mathrm{cell}_I(x)$, this means one of:

- $d = 0$ (up): $c' = c$ and $r' < r$;
- $d = 1$ (right): $r' = r$ and $c < c'$;
- $d = 2$ (down): $c' = c$ and $r < r'$;
- $d = 3$ (left): $r' = r$ and $c' < c$.

If $d \ge 4$, no cell lies along the arrow of $x$.
