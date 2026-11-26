# Orthogonalization of measurements in a full matrix algebra (de la Salle)

Let $\iota$ be finite, $(M_a)_{a\in\alpha}$ a measurement in $M_\iota(\mathbb{C})$ with finite outcome set, and $\varphi$ any state on $M_\iota(\mathbb{C})$. There is a projective measurement $(P_a)_{a\in\alpha}$ in the same algebra $M_\iota(\mathbb{C})$ with

$$
\sum_a\|M_a-P_a\|_\varphi^2\le9\Big(1-\sum_a\operatorname{Re}\varphi(M_a^2)\Big).
$$

In particular, if $\sum_a\operatorname{Re}\varphi(M_a^2)\ge1-\varepsilon$ then $M$ is within $9\varepsilon$ of a projective measurement in squared state distance; the dependence on $\varepsilon$ is linear and there is no change of dimension.

## Proof sketch

Diagonalize each effect and select $|\iota|$ eigenpairs of largest weight $\lambda\varphi(\text{eigenprojection})$, giving projections $q_a$ commuting with $M_a$ of total rank $|\iota|$ with $\varphi(\sum_aM_a^2)\le\varphi(\sum_aq_aM_a)$; the eigenvalues form a fractional selection of total mass $|\iota|$ and the largest weights dominate it. A polar decomposition of the column operator built from $\sqrt{q_aM_a}$ produces $h$ and a projective $P$ with $h^2 = \sum_aq_aM_a$ and $hP_ah = q_aM_a$. The orthogonalization estimate then gives the bound.

## Depends on

- [Measurements, agreement and character observables in a star-ordered algebra](algebraic-measurements-and-agreement.md)

## Proof depends on

- [The orthogonalization estimate from a dilation](orthogonalization-estimate.md)
- [Polar decomposition of a complex square matrix](../../../LinearAlgebra/matrix-decompositions/polar-decomposition/polar-decomposition-theorem/exists-unitary-group-pos-semidef.md)

## Sources

- M. de la Salle, "Orthogonalization of positive operator valued measures", Comptes Rendus. Mathematique 360:549-560, 2022.
