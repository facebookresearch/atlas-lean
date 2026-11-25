# $(\mathrm{GL}_m, \mathrm{GL}_n)$ duality on symmetric algebras of tensor products

Let $m, n \ge 1$. The group $\mathrm{GL}_m(\mathbb{C}) \times \mathrm{GL}_n(\mathbb{C})$ acts on
$\mathbb{C}^m \otimes \mathbb{C}^n$, the space of complex $m \times n$ matrices, through the tensor
product of the standard representations, and hence on the symmetric algebra
$S(\mathbb{C}^m \otimes \mathbb{C}^n)$, a polynomial algebra in $mn$ variables. For a partition
$\lambda = (\lambda_1, \dots, \lambda_l)$ with at most $k$ parts let $V_k^\lambda$ be the irreducible
representation of $\mathrm{GL}_k(\mathbb{C})$ (or of $\mathfrak{gl}_k$) with highest weight
$(\lambda_1, \dots, \lambda_l, 0, \dots, 0)$. Then, as a representation of
$\mathrm{GL}_m(\mathbb{C}) \times \mathrm{GL}_n(\mathbb{C})$,

$$S(\mathbb{C}^m \otimes \mathbb{C}^n) \cong \bigoplus_{\lambda} V_m^\lambda \otimes V_n^\lambda,$$

the sum running over the partitions $\lambda$ with at most $\min(m, n)$ parts. The decomposition is
multiplicity-free: each summand is irreducible and the summands are pairwise non-isomorphic. Thus the
irreducible representations of $\mathrm{GL}_m$ and of $\mathrm{GL}_n$ that occur are matched one to one
by $V_m^\lambda \leftrightarrow V_n^\lambda$, an instance of Howe duality; Cheng and Wang give the
highest weight vectors of the summands as products of certain determinants in the variables.

Cheng and Wang state the decomposition for $\mathfrak{gl}(m) \times \mathfrak{gl}(n)$ and recall it as
the classical $\mathrm{GL}(m) \times \mathrm{GL}(n)$-duality of Howe; the representations involved are
polynomial representations of the connected groups $\mathrm{GL}_m(\mathbb{C})$ and
$\mathrm{GL}_n(\mathbb{C})$, so the decomposition is the same for the groups.

## Sources

- S.-J. Cheng and W. Wang, *Howe duality for Lie superalgebras*, arXiv:math/0008093v1 (2000), Section 2
  ("The Classical Picture"): the decomposition of $S(\mathbb{C}^m \otimes \mathbb{C}^n)$ as a
  $\mathfrak{gl}(m) \times \mathfrak{gl}(n)$-module over Young diagrams of length at most $\min(m, n)$,
  and the highest weight vectors (2.2); the Introduction for the multiplicity-free property.
- R. Howe, *Perspectives on invariant theory: Schur duality, multiplicity-free actions and beyond*, The
  Schur Lectures, Israel Math. Conf. Proc. 8, Tel Aviv (1992), 1–182, the reference Cheng and Wang give
  for the classical duality.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, for polynomial functions on matrices and for the groups
  $\mathrm{GL}_m(\mathbb{C}) \times \mathrm{GL}_n(\mathbb{C})$ and $\mathrm{U}(m) \times \mathrm{U}(n)$,
  as `GlobalTheory.Published.GLHoweDuality`.
