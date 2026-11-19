# Lattice points visited by the outside connector

For $d_x, d_y, t \in \mathbb{Z}$, write $a^+ = \max(a, 0)$. The vertex list is the concatenation of

- the origin $(0, 0)$;
- the points $(1, k)$ for $k = 0, \dots, (t - d_y)^+ - 1$;
- the points $(1 - k, t - d_y)$ for $k = 0, \dots, (d_x + 2)^+ - 1$;
- the points $(-d_x - 1, t - d_y - k)$ for $k = 0, \dots, t^+ - 1$;
- the point $(-d_x - 1, -d_y)$.
