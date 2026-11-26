# Distinct CSS codewords are orthogonal

If $w_1 + w_2 \notin C_1^{\perp}$, then

$$\langle c_{w_1} | c_{w_2} \rangle = \sum_{v} \overline{c_{w_1}(v)}\, c_{w_2}(v) = 0.$$

The inner product is $\sum_{v \in C_1} (-1)^{v \cdot (w_1 + w_2)}$, a
[character sum](sum-sign-eq-zero.md) that vanishes because some $v \in C_1$ has
$v \cdot (w_1 + w_2) = 1$. Together with
[the coset dependence](codeword-eq-of-add-mem-dual.md), the $|c_w\rangle$ for
$w \in \mathbb{F}_2^n / C_1^{\perp}$ form an orthogonal basis of the span of $\{|v\rangle : v \in C_1\}$.

## Sources

- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Section III, after equation (2).
