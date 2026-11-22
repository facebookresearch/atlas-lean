# Branching from $\mathrm{GL}_{n+1}(\mathbb{C})$ to $\mathrm{GL}_n(\mathbb{C})$

Let $n \ge 1$. The irreducible finite-dimensional holomorphic representations of
$\mathrm{GL}_{n+1}(\mathbb{C})$ are the representations $L(\lambda)$ of highest weight
$\lambda = (\lambda_1, \dots, \lambda_{n+1}) \in \mathbb{Z}^{n+1}$ with
$\lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_{n+1}$, and similarly for $\mathrm{GL}_n(\mathbb{C})$.
Embed $\mathrm{GL}_n(\mathbb{C})$ in $\mathrm{GL}_{n+1}(\mathbb{C})$ as the upper-left block. Then the
restriction of $L(\lambda)$ to $\mathrm{GL}_n(\mathbb{C})$ is isomorphic to

$$L(\lambda)\big|_{\mathrm{GL}_n(\mathbb{C})} \cong \bigoplus_{\mu} L(\mu),$$

the sum running over the $\mu = (\mu_1, \dots, \mu_n) \in \mathbb{Z}^n$ that interlace $\lambda$:

$$\lambda_1 \ge \mu_1 \ge \lambda_2 \ge \mu_2 \ge \dots \ge \lambda_n \ge \mu_n \ge \lambda_{n+1}.$$

The summands are pairwise non-isomorphic: each $L(\mu)$ with $\mu$ interlacing $\lambda$ occurs exactly
once, and no other irreducible representation of $\mathrm{GL}_n(\mathbb{C})$ occurs.

Molev states the rule for the Lie algebras, $\mathfrak{gl}_{n+1} \downarrow \mathfrak{gl}_n$, whose
finite-dimensional irreducible representations have highest weights $\lambda \in \mathbb{C}^{n+1}$ with
$\lambda_i - \lambda_{i+1} \in \mathbb{Z}_{\ge 0}$; the holomorphic representations of
$\mathrm{GL}_{n+1}(\mathbb{C})$ are those with integral $\lambda$. Twisting by a power of the
determinant reduces the rule to the case where $\lambda$ is a partition. Then the character of
$L(\lambda)$ on an element with eigenvalues $x_1, \dots, x_{n+1}$ is the Schur polynomial
$s_\lambda(x_1, \dots, x_{n+1})$, and restricting to $\mathrm{GL}_n(\mathbb{C})$ amounts to setting
$x_{n+1} = 1$, which turns $s_\lambda$ into the sum of the $s_\mu(x_1, \dots, x_n)$ over the interlacing
$\mu$. Iterating the rule down the chain
$\mathrm{GL}_1 \subset \mathrm{GL}_2 \subset \dots \subset \mathrm{GL}_{n+1}$ gives the Gelfand–Tsetlin
basis of $L(\lambda)$, indexed by patterns.

## Sources

- A. I. Molev, *Gelfand–Tsetlin bases for classical Lie algebras*, arXiv:math/0211289v2 (2002), in
  *Handbook of Algebra*, Section 2: Theorem 2.1 (the branching rule for
  $\mathfrak{gl}_n \downarrow \mathfrak{gl}_{n-1}$, with the betweenness conditions (2.2)) and the
  discussion after it (Schur polynomials and restriction to $\mathrm{GL}_{n-1}$; the rule implicit in
  Gelfand and Tsetlin, proved by Zhelobenko; two other proofs in Goodman and Wallach, Chapters 8
  and 12); Theorem 2.3 (patterns).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, for $\mathrm{GL}_n(\mathbb{C}) \subset \mathrm{GL}_{n+1}(\mathbb{C})$ and
  for $\mathrm{U}(n) \subset \mathrm{U}(n+1)$, as `GlobalTheory.Published.WeylBranching`.
