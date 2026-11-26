# Local orthogonalization in tensor-product strategies

Let $\varphi$ be a state on $M_{\iota\times\kappa}(\mathbb{C})$, $M$ a measurement in $M_\iota(\mathbb{C})$ and $N$ a measurement in $M_\kappa(\mathbb{C})$, with $\sum_a\operatorname{Re}\varphi(M_a^2\otimes I)\ge1-\varepsilon$ and $\sum_b\operatorname{Re}\varphi(I\otimes N_b^2)\ge1-\varepsilon'$. There are projective measurements $P$ in $M_\iota(\mathbb{C})$ and $R$ in $M_\kappa(\mathbb{C})$ with

$$
\sum_a\|(M_a-P_a)\otimes I\|_\varphi^2\le9\varepsilon,\qquad\sum_b\|I\otimes(N_b-R_b)\|_\varphi^2\le9\varepsilon',
$$

so $P_a\otimes I$ and $I\otimes R_b$ commute. If $M$ has outcomes in $\{0,1\}^n$, then $P$ can be chosen with unitary, exactly linear character observables and $\mathbb{E}_a\|(\chi_M(a)-\chi_P(a))\otimes I\|_\varphi^2\le9\varepsilon$.

## Proof sketch

Pull $\varphi$ back along the star-homomorphisms $X\mapsto X\otimes I$ and $Y\mapsto I\otimes Y$, which are monotone; the pulled-back states measure exactly the norms appearing in the hypotheses. Apply the orthogonalization theorem on each factor. For characters, $\chi$ is linear in the effects, so Parseval in the state, $\mathbb{E}_a\|\sum_x(-1)^{a\cdot x}D_x\|_\varphi^2 = \sum_x\|D_x\|_\varphi^2$, transfers the bound.

## Depends on

- [Measurements, agreement and character observables in a star-ordered algebra](algebraic-measurements-and-agreement.md)

## Proof depends on

- [Orthogonalization of measurements in a full matrix algebra (de la Salle)](orthogonalization-of-measurements.md)

## Sources

- M. de la Salle, "Orthogonalization of positive operator valued measures", Comptes Rendus. Mathematique 360:549-560, 2022.
- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017.
