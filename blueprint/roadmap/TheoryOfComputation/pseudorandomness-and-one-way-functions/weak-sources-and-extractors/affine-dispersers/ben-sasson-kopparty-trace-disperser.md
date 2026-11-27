# Ben-Sasson–Kopparty: the trace of an elementary symmetric polynomial is an affine disperser

Let $F$ be a field with $2^n$ elements in which every proper subfield has at most $2^s$ elements, let $\mu \in F^\times$, $r \ge 1$ and $t \ge 1$. Define $\mathrm{TS}(x) = \mathrm{Tr}_{F/\mathbb{F}_2}\bigl(\mu \, e_t(y_0, \dots, y_{r-1})\bigr)$ for $x \in F^r$, where $y_i = x_i^{2^{r+1-i} - 1}$ and $e_t$ is the $t$-th elementary symmetric polynomial. Then $\mathrm{TS}$ is nonconstant on every $\mathbb{F}_2$-affine subspace $A \subseteq F^r$ with

$$
\dim A > r\max(r+1, s) + r(r+1) + nt + \lfloor nr/t \rfloor .
$$

Reading $r$ field elements from $N$ input bits in a fixed $\mathbb{F}_2$-basis, the induced Boolean function on $\{0,1\}^N$ is nonconstant on every affine subspace of dimension greater than $N - rn$ plus the same bound. The algebraic core: for $\mathbb{F}_2$-subspaces $Y_i \subseteq F$ of dimensions $d_i > s$ and integers $2 \le k_i < d_i$ with $\sum_i(d_i - k_i) \ge n + 1 - \max_i d_i$, every nonzero functional $z \mapsto \mathrm{Tr}(\mu z)$ is nonzero on some product $\prod_i \Delta(u_i)$ of Moore determinants of families $u_i \in Y_i^{k_i}$.

## Proof sketch

Parametrize each pivot subspace by its subspace polynomial; the map $w \mapsto \mathrm{Tr}(\mu\prod_i\Delta(Q_i\circ w_i))$ is a reduced polynomial whose coefficient at a suitably chosen monomial is a sum over Frobenius rotations of products of permanents. Choosing exponents so that the unrotated matrices are triangular with nonzero diagonal while every nontrivial rotation has a zero row isolates a nonzero coefficient, and a reduced polynomial with a nonzero coefficient is a nonzero function.

## Depends on

- [Affine dispersers](../../../circuit-complexity/circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/gate-elimination-and-explicit-lower-bounds/affine-dispersers.md)
- [The Galois field with pⁿ elements](../../../../FieldTheory/finite-fields/finite-field-existence.md)

## Sources

- E. Ben-Sasson and S. Kopparty, "Affine Dispersers from Subspace Polynomials", SIAM Journal on Computing, 2012.
