# Representation-theoretic occurrence and multiplicity obstructions

The coordinate ring $\mathbb{C}[\overline{\mathrm{GL}_{n^2}\cdot \det_n}]$ is a graded $\mathrm{GL}_{n^2}$-representation; for a partition $\lambda$ of $nD$ with at most $n^2$ parts let $\delta_\lambda(n)$ be the multiplicity of the irreducible Weyl module $V_\lambda$ in its degree-$D$ component, and $\gamma_\lambda(m,n)$ the corresponding multiplicity for $\overline{\mathrm{GL}_{n^2}\cdot \ell^{n-m}\mathrm{perm}_m}$. A partition $\lambda$ is a **multiplicity obstruction** if $\delta_\lambda(n) < \gamma_\lambda(m,n)$, and an **occurrence obstruction** if $\delta_\lambda(n) = 0 < \gamma_\lambda(m,n)$. The existence of any multiplicity obstruction implies $\ell^{n-m}\mathrm{perm}_m \notin \overline{\mathrm{GL}_{n^2}\cdot\det_n}$, i.e. $\underline{\mathrm{dc}}(\mathrm{perm}_m) > n$.

## Depends on

- [Determinantal complexity and the padded permanent orbit closure problem](det-vs-perm-gct.md)
- [Schur–Weyl duality: the general linear side](../../../RepresentationTheory/lie-and-topological-representations/schur-weyl-duality/gl-action-range-eq-centralizer-sym-actio.md)

## Sources

- K. D. Mulmuley, M. Sohoni, "Geometric complexity theory I: an approach to the P vs. NP and related problems", SIAM Journal on Computing 31 (2001) 496-526.
- P. Bürgisser, C. Ikenmeyer, G. Panova, "No occurrence obstructions in geometric complexity theory", Journal of the American Mathematical Society 32 (2019) 163-193; FOCS (2016), arXiv:1604.06431.
