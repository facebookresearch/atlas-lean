# Interaction between rows of the grid row network

Consider the row network built from $\Lambda, \Delta, R, T, \mathrm{top}, \mathrm{bot}, \kappa, L$,
and let $G_\omega$ be kernels with $G_\omega(x, y, u, v) = \sum_{\theta \in T_\omega}
\mathrm{top}_\omega(x, y, \theta) \, \mathrm{bot}_\omega(u, v, \theta)$ for all $\omega, x, y, u, v$.
For rows $a < b$ and any families $z, z'$ (not necessarily allowed states), the interaction is

$$I_{a,b}(z, z') = \prod_{i} \bigl[z_i(b, i) = z'_i(a, i) \text{ and } z_i(b, i) \in \Lambda\bigr] \cdot \prod_{k} G_{((a,b),k)}\bigl(z_{k_1}(b, k_2), z_{k_2}(b, k_1), z'_{k_1}(a, k_2), z'_{k_2}(a, k_1)\bigr),$$

with $i$ over the columns and $k = (k_1, k_2)$ over the column pairs with $k_1 < k_2$.
