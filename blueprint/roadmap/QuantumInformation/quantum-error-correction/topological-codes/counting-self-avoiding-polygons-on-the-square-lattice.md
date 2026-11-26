# Counting self-avoiding polygons on the square lattice

Let $n_{\mathrm{SAP}}(\ell)$ be the number of self-avoiding closed walks (self-avoiding polygons) of length $\ell$ on the
square lattice $\mathbb{Z}^2$ starting at a fixed vertex. Then $n_{\mathrm{SAP}}(\ell) \le 4 \cdot 3^{\ell - 1}$, since the
first step has $4$ choices and each later step at most $3$; and $n_{\mathrm{SAP}}(\ell) \le P_2(\ell)\, \mu_2^{\ell}$ for a
polynomial $P_2$, where $\mu_2 \approx 2.638$ is the connective constant of self-avoiding walks on $\mathbb{Z}^2$. In
$d$ dimensions the first bound is $2d (2d - 1)^{\ell - 1}$, and on the cubic lattice $\mu_3 \approx 4.684$.

## Expansion

A sound expansion adds the definition of the connective constant $\mu_2 = \lim_{n} c_n^{1/n}$ of self-avoiding walks
(the limit exists by submultiplicativity of the walk counts $c_n$) and the bound for polygons, which Dennis, Kitaev,
Landahl and Preskill cite from the self-avoiding walk literature; the elementary bound $4 \cdot 3^{\ell - 1}$ needs no
prerequisite and already gives a threshold with $\mu_2$ replaced by $3$.

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V.C, equations (56)–(58).
