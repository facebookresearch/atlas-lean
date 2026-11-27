# Landsberg–Manivel–Ressayre: quadratic lower bound on border determinantal complexity

For every $m \ge 3$, the border determinantal complexity of the permanent satisfies

$$
\underline{\mathrm{dc}}(\mathrm{perm}_m) \ge \frac{m^2}{2}.
$$

The bound is proved by exhibiting equations, coming from the degeneracy of the dual variety of the determinant hypersurface, that vanish on $\overline{\mathrm{GL}_{n^2}\cdot\det_n}$ for $n < m^2/2$ but not at the padded permanent.

## Proof sketch

The dual variety of the determinant hypersurface is the set of rank-one matrices, which is highly degenerate. Degeneracy of the dual is a closed condition on the Hessian of the polynomial at general points, inherited by every point of the orbit closure, and is expressed by the vanishing of minors of the Hessian of $f$ restricted to $\{f = 0\}$. For the padded permanent the corresponding Hessian minors are nonzero as long as $n < m^2/2$.

## Depends on

- [Determinantal complexity and the padded permanent orbit closure problem](det-vs-perm-gct.md)

## Sources

- J. M. Landsberg, L. Manivel, N. Ressayre, "Hypersurfaces with degenerate duals and the geometric complexity theory program", Commentarii Mathematici Helvetici 88 (2013) 469-484.
