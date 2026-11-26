# CHEVALLEY_p, GENERAL-CHEVALLEY_p and CHEVALLEY-WITH-SYMMETRY_p: explicit search problems from the Chevalley–Warning theorem

Let $p$ be prime and $\mathbf f=(f_1,\dots,f_m)\in\mathbb F_p[x_1,\dots,x_n]^m$ be **explicit** (each $f_i$ written as a sum of monic monomials), with common zero set $\mathcal V_{\mathbf f}\subseteq\mathbb F_p^n$. Put

$$
\mathrm{CW}_{\mathbf f}(x)=\prod_{i=1}^m\bigl(1-f_i(x)^{p-1}\bigr)\bmod\{x_j^p-x_j\}_j .
$$

A **monic monomial** of $\mathrm{CW}_{\mathbf f}$ is one obtained by symbolically expanding the product (no cancellation), described succinctly by at most $m(p-1)$ monomials of the $f_i$; it is **max-degree** if it equals $\prod_jx_j^{p-1}$.

- CHEVALLEY$_p$: given $\mathbf f$ and $x^*\in\mathcal V_{\mathbf f}$, output a witness that $\sum_i\deg f_i<n$ fails, or $x\in\mathcal V_{\mathbf f}\setminus\{x^*\}$.
- GENERAL-CHEVALLEY$_p$: given $\mathbf f$ and $x^*\in\mathcal V_{\mathbf f}$, output a max-degree monic monomial of $\mathrm{CW}_{\mathbf f}$, or $x\in\mathcal V_{\mathbf f}\setminus\{x^*\}$.
- CHEVALLEY-WITH-SYMMETRY$_p$: given explicit systems $\mathbf g,\mathbf h$, $x^*\in\mathcal V_{(\mathbf g,\mathbf h)}$ and a permutation $\sigma\in S_n$ of order $p$ acting on coordinates, output a max-degree monic monomial of $\mathrm{CW}_{\mathbf g}$; or $x\in\mathcal V_{\mathbf g}\setminus\mathcal V_{\mathbf h}$ with $\sigma(x)\notin(\mathcal V_{\mathbf g}\setminus\mathcal V_{\mathbf h})\setminus\{x\}$; or $x\in\mathcal V_{(\mathbf g,\mathbf h)}\setminus\{x^*\}$.

These problems are natural: no circuit or machine appears in the input.

## Depends on

- [Chevalley–Warning theorem, existence form](../../../../Combinatorics/additive-combinatorics/combinatorial-nullstellensatz/exists-ne-common-zero.md)

## Sources

- Mika Göös, Pritish Kamath, Katerina Sotiraki and Manolis Zampetakis, "On the Complexity of Modulo-q Arguments and the Chevalley–Warning Theorem", CCC (2020), arXiv:1912.04467.
