# The Conway knot is topologically slice

Let $K$ be the PL knot traced by the braid closure
on $4$ strands of the braid word
$\sigma_1^{-2} \sigma_2 \sigma_1^{-1} \sigma_2 \sigma_1^{-1} \sigma_3 \sigma_2^{-2} \sigma_3^2$
for the Conway knot 11n34. Then $K$ is topologically slice: there is a smooth knot $J$ whose
image is unoriented topologically ambient isotopic in $\mathbb{R}^3$ to the image of $K$, and $J$
is topologically slice.

This follows from Freedman's theorem that every knot with trivial Alexander polynomial is
topologically slice, since the Conway knot has $\Delta_K(t) = 1$.

## Sources

- Freedman, *The topology of four-dimensional manifolds*, J. Diff. Geom. 17 (1982). See also Freedman-Quinn, *Topology of 4-Manifolds*, Princeton 1990. Problem `conway_knot_topologically_slice` of the lean-eval benchmark.
