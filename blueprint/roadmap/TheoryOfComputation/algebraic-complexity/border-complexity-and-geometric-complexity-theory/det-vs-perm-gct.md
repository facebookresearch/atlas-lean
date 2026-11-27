# Determinantal complexity and the padded permanent orbit closure problem

For a polynomial $f$, its **determinantal complexity** $\mathrm{dc}(f)$ is the least $n$ such that $f$ is an affine projection of $\det_n$, i.e. $f(x) = \det(A(x))$ for an $n \times n$ matrix $A$ of affine linear forms. Its **border determinantal complexity** $\underline{\mathrm{dc}}(f)$ is the border version. With a new variable $\ell$, the **padded permanent** is $\ell^{n-m}\,\mathrm{perm}_m \in \mathbb{C}[\mathbb{C}^{n \times n}]_n$. Then $\underline{\mathrm{dc}}(\mathrm{perm}_m) \le n$ if and only if

$$
\ell^{n-m}\,\mathrm{perm}_m \in \overline{\mathrm{GL}_{n^2} \cdot \det_n}.
$$

The **permanent versus determinant conjecture** (Valiant) asserts $\mathrm{dc}(\mathrm{perm}_m) = m^{\omega(1)}$; Mulmuley and Sohoni's border version asserts $\underline{\mathrm{dc}}(\mathrm{perm}_m) = m^{\omega(1)}$.

## Depends on

- [Orbit closures and border complexity of polynomials](orbit-closure-border.md)
- [Valiant's VP versus VNP conjecture](../valiant-s-vp-versus-vnp-conjecture.md)

## Sources

- K. D. Mulmuley, M. Sohoni, "Geometric complexity theory I: an approach to the P vs. NP and related problems", SIAM Journal on Computing 31 (2001) 496-526.
- L. G. Valiant, "Completeness classes in algebra", STOC (1979).
- J. M. Landsberg, L. Manivel, N. Ressayre, "Hypersurfaces with degenerate duals and the geometric complexity theory program", Commentarii Mathematici Helvetici 88 (2013) 469-484.
