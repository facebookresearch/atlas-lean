# Fenn–Rourke–Sanderson conjecture (Ohtsuki Conjecture 5.12)

The statement that for every odd prime $p$ the third rack homology of the dihedral quandle $R_p$ is $\mathbb{Z} \oplus \mathbb{Z}/p$ as an abelian group. For a natural number $p$, the dihedral quandle $R_p$ is $\mathbb{Z}/p$ with the operation $a * b = 2b - a$. The rack chain group $C_m(R_p)$ is the free abelian group on the $m$-tuples $(x_1, \dots, x_m)$ of elements of $\mathbb{Z}/p$. The rack boundary $\partial : C_{m+1}(R_p) \to C_m(R_p)$ is

$$\partial(x_1, \dots, x_{m+1}) = \sum_{i=2}^{m+1} (-1)^i \bigl( (x_1, \dots, \widehat{x_i}, \dots, x_{m+1}) - (x_1 * x_i, \dots, x_{i-1} * x_i, x_{i+1}, \dots, x_{m+1}) \bigr),$$

where $\widehat{x_i}$ means that $x_i$ is omitted. The third rack homology group is $H_3^R(R_p) = \ker(\partial : C_3 \to C_2) / \operatorname{im}(\partial : C_4 \to C_3)$. The source states the conjecture for every prime $p$; at $p = 2$ the quandle $R_2$ is trivial, all boundaries vanish and $H_3^R(R_2) \cong \mathbb{Z}^8$, so only odd primes are meant.

## Sources

- T. Ohtsuki (ed.), Problems on invariants of knots and 3-manifolds, Geom. Topol. Monogr. 4 (2002), Conjecture 5.12 (R. Fenn, C. Rourke, B. Sanderson).
