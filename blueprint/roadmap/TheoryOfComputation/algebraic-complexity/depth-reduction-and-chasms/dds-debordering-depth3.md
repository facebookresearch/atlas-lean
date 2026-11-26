# Dutta–Dwivedi–Saxena: debordering depth-three circuits of bounded top fan-in

For every fixed $k \in \mathbb{N}$, every polynomial in the border of $\Sigma^{[k]}\Pi\Sigma$ circuits of size $s$ over $\mathbb{C}$ (depth-three circuits with top fan-in $k$) is computed exactly by an algebraic branching program of size $s^{O_k(1)}$. Consequently the border class $\overline{\Sigma^{[k]}\Pi\Sigma}$ is contained in $\mathrm{VBP}$, and there are explicit quasi-polynomial-time hitting sets for it.

## Proof sketch

Induct on $k$ using a ``differentiation-and-division'' process: divide by one product gate and differentiate to reduce the top fan-in, keeping track of the approximation parameter $\varepsilon$ via formal power series in $\varepsilon$ truncated at a bounded order. The resulting expressions are compositions of polynomials with power series that can be truncated and computed by small ABPs; hitting sets follow from known hitting sets for ABPs of the resulting low-variable form.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)
- [Valiant's VP versus VNP conjecture](../valiant-s-vp-versus-vnp-conjecture.md)

## Proof depends on

- [Kumar: every homogeneous polynomial lies in the border of top-fan-in d+1 depth-three circuits](kumar-border-depth3.md)

## Sources

- P. Dutta, P. Dwivedi, N. Saxena, "Demystifying the border of depth-3 algebraic circuits", FOCS (2021).
