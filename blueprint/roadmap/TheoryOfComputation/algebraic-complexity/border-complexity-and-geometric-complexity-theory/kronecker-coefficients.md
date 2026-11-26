# Kronecker coefficients of the symmetric group

For partitions $\lambda, \mu, \nu$ of $N$, the **Kronecker coefficient** $g(\lambda, \mu, \nu)$ is the multiplicity of the irreducible $S_N$-representation $[\nu]$ in the tensor product $[\lambda] \otimes [\mu]$:

$$
g(\lambda, \mu, \nu) = \frac{1}{N!} \sum_{\pi \in S_N} \chi_\lambda(\pi)\chi_\mu(\pi)\chi_\nu(\pi).
$$

Equivalently, by Schur-Weyl duality, $g(\lambda,\mu,\nu)$ is the multiplicity of $V_\lambda \otimes V_\mu$ in the restriction of $V_\nu(\mathrm{GL}_{ab})$ to $\mathrm{GL}_a \times \mathrm{GL}_b$. Kronecker coefficients with $\lambda = \mu = (n^{d})$ a rectangle govern the multiplicities in the coordinate ring of the orbit of $\det_n$.

## Depends on

- [Schur–Weyl duality: the general linear side](../../../RepresentationTheory/lie-and-topological-representations/schur-weyl-duality/gl-action-range-eq-centralizer-sym-actio.md)

## Sources

- P. Bürgisser, C. Ikenmeyer, G. Panova, "No occurrence obstructions in geometric complexity theory", Journal of the American Mathematical Society 32 (2019) 163-193; FOCS (2016), arXiv:1604.06431.
- C. Ikenmeyer, K. D. Mulmuley, M. Walter, "On vanishing of Kronecker coefficients", Computational Complexity 26 (2017) 949-992, arXiv:1507.02955.
- C. Ikenmeyer, G. Panova, "Rectangular Kronecker coefficients and plethysms in geometric complexity theory", Advances in Mathematics 319 (2017) 40-66; FOCS (2016).
