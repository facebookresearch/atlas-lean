# Rounding approximately linear observables to exactly linear ones on the same space

Let $\varphi$ be a state on $M_\iota(\mathbb{C})$ and $A(a)$, $a\in\{0,1\}^n$, $\pm1$ observables in $M_\iota(\mathbb{C})$ with $\mathbb{E}_{a,b}\operatorname{Re}\varphi(A(a)A(b)A(a+b))\ge1-\delta$. There is a projective measurement $P$ in $M_\iota(\mathbb{C})$ with outcomes $\{0,1\}^n$ whose character observables $\chi_P(a)$ are unitary and exactly linear, $\chi_P(a)\chi_P(a') = \chi_P(a+a')$, and

$$
\mathbb{E}_a\|A(a)-\chi_P(a)\|_\varphi^2\le40\,\delta .
$$

For self-adjoint contractions $A(a)$ the same holds with $48\delta$. Since the bound holds in every state, the same conclusion holds for one party of a tensor-product strategy, with $A(a)\otimes I$ and $\chi_P(a)\otimes I$.

## Proof sketch

The Fourier measurement is almost projective with defect $2\delta$, and its characters are within $2\delta$ of $A$ on average. Orthogonalizing it in place gives a projective $P$ whose characters are within $9\cdot2\delta$ of the Fourier characters, by Parseval in the state. The triangle inequality for squared distances gives $2(2\delta+18\delta) = 40\delta$. This replaces the ancilla dilation of the original argument by in-place orthogonalization, at the cost of the constant.

## Depends on

- [Measurements, agreement and character observables in a star-ordered algebra](../states-and-measurements-on-operator-algebras/algebraic-measurements-and-agreement.md)

## Proof depends on

- [Near-linear observables have an almost projective Fourier measurement](fourier-measurement-near-linear.md)
- [Orthogonalization of measurements in a full matrix algebra (de la Salle)](../states-and-measurements-on-operator-algebras/orthogonalization-of-measurements.md)
- [Local orthogonalization in tensor-product strategies](../states-and-measurements-on-operator-algebras/local-orthogonalization-tensor-product.md)

## Sources

- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017.
- M. de la Salle, "Orthogonalization of positive operator valued measures", Comptes Rendus. Mathematique 360:549-560, 2022.
