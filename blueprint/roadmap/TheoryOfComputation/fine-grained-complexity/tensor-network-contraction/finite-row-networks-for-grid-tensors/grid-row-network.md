# Row network of a grid tensor

Let $\rho$ (rows) and $\gamma$ (columns) be finite linear orders, $\Lambda, \Delta$ finite sets of
labels in $A$, $R$ a complete-graph tensor instance on the cells $\rho \times \gamma$, and for each
$\omega = ((a, b), k) \in (\rho \times \rho) \times (\gamma \times \gamma)$ a finite set $T_\omega$
of cut labels, integer factors $\mathrm{top}_\omega(x, y, \theta)$ and
$\mathrm{bot}_\omega(u, v, \theta)$ and a capacity $\kappa_\omega \in \mathbb{N}$; let
$L \in \mathbb{N}$. The row network is the factored tensor network on the vertex set $\rho$ given
as follows; below $k = (k_1, k_2)$ ranges over the column pairs with $k_1 < k_2$.

- A state at row $a$ is a family $z = (z_i)_{i \in \gamma}$ of maps $z_i : \rho \times \gamma \to A$
  (the half-edge labels at the cell $(a, i)$); it is allowed when $z_i(a, i) \in \Delta$ and
  $z_i(w) \in \Lambda$ for $w \ne (a, i)$.
- The weight is $W_a(z) = \prod_i R_{(a,i)}(z_i) \cdot \prod_{q_1 < q_2}
  [z_{q_1}(a, q_2) = z_{q_2}(a, q_1)]$.
- For $a < b$, the label set at $(a, b)$ consists of the pairs $(\theta_1, \theta_2)$ with
  $\theta_1(i) \in \Lambda$ for every column $i$ and $\theta_2(k) \in T_{((a,b),k)}$ for every $k$;
  for $a \not< b$ it is empty.
- For $a < b$, the factor is $f_{a,b}(z, \theta) = \prod_i [z_i(b, i) = \theta_1(i)] \cdot \prod_k
  \mathrm{top}_{((a,b),k)}(z_{k_1}(b, k_2), z_{k_2}(b, k_1), \theta_2(k))$; for $a \not< b$ it is
  $\prod_i [z_i(b, i) = \theta_1(i)] \cdot \prod_k \mathrm{bot}_{((b,a),k)}(z_{k_1}(b, k_2),
  z_{k_2}(b, k_1), \theta_2(k))$.
- The capacity is $c_{a,b} = |\gamma| L + \sum_k \kappa_{((\min(a,b), \max(a,b)), k)}$.

Here $[\cdot]$ is $1$ if the equality holds and $0$ otherwise.
