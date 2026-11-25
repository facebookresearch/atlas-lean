# Cells on a Yosenabe arrow

In a Yosenabe puzzle, let $x = (x_1, x_2)$, $t = (t_1, t_2)$ and $z = (z_1, z_2)$ be cells (row, column). The cell $z$ is on the line of the arrow from $x$ to its tip $t$ when $z \ne x$ and either

- $z_1 = x_1 = t_1$ and $\min(x_2, t_2) \le z_2 \le \max(x_2, t_2)$ (a horizontal arrow), or
- $z_2 = x_2 = t_2$ and $\min(x_1, t_1) \le z_1 \le \max(x_1, t_1)$ (a vertical arrow).

So the line consists of the cells from $x$ (excluded) to $t$ (included); if $t$ is in neither the row nor the column of $x$, no cell is on the line.
