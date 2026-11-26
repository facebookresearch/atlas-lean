# The rank measure of iterated matrix multiplication

For a balanced schedule that differentiates in $k$ of the $n$ matrix layers and multiplies in the others (layers ordered as $VU^{\ell_1}VU^{\ell_2}\cdots VU^{\ell_k}$ with balanced gaps), the rank measure of $\mathrm{IMM}_{n,n}$ is at least $D\,e^{-C\sqrt n}$, where $D$ is the dimension of the slice on which the operator acts and $C$ is an absolute constant.

## Proof sketch

Write the operator's matrix $F$ in normalized monomial bases as a sum over paths of the matrix product; compute the first trace moment $\operatorname{tr}F^TF$ exactly (distinct paths map basis vectors to distinct basis vectors) and bound the second moment $\operatorname{tr}(F^TF)^2$ by a sum over four paths paired layer by layer, weighted by type words; then $\operatorname{rank}F\ge(\operatorname{tr}F^TF)^2/\operatorname{tr}(F^TF)^2$.

## Depends on

- [A rank measure from differentiation and multiplication](depth-five-rank-measure.md)

## Proof depends on

- [A rank lower bound from two trace moments](../../../LinearAlgebra/matrix-algebra/rank-bounds-for-complexity/rank-lower-bound-from-trace-moments.md)

## Sources

- OpenAI, "Homogeneous Depth-Five Lower Bounds for Iterated Matrix Multiplication", Preprint, 2026.
