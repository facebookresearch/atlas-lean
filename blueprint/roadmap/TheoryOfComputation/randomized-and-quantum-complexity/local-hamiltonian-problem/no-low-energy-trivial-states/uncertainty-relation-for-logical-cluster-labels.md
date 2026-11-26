# Uncertainty relation for complementary logical measurements

Let $\{P_i\}_{i=1}^{D}$ and $\{Q_j\}_{j=1}^{D}$ be projective measurements of a $D$-dimensional register in two mutually unbiased bases, $|\langle e_i | f_j\rangle|^2 = 1/D$. For every state $\sigma$,

$$
\max_i \mathrm{Tr}(P_i\sigma) + \max_j \mathrm{Tr}(Q_j\sigma) \le 1 + \frac{1}{\sqrt D} .
$$

Applied to the $k$ logical qubits of a CSS code ($D = 2^k$), the $X$-cluster label and the $Z$-cluster label of any state cannot both be determined with probability close to $1$.

## Proof sketch

For unit vectors $e, f$ with $|\langle e|f\rangle| = 1/\sqrt D$ the operator $|e\rangle\langle e| + |f\rangle\langle f|$ has largest eigenvalue $1 + |\langle e | f \rangle| = 1 + 1/\sqrt D$, hence $\langle \psi| (|e\rangle\langle e| + |f\rangle\langle f|)|\psi\rangle \le 1 + 1/\sqrt D$ for every unit $\psi$; extend to mixed states by convexity. The logical $X$- and $Z$-bases of a CSS code are mutually unbiased on the logical register.

## Depends on

- [CSS codeword](../../../../QuantumInformation/quantum-error-correction/css-codes/codeword.md)

## Sources

- Hans Maassen, J. B. M. Uffink, "Generalized entropic uncertainty relations", Physical Review Letters 60 (1988).
- Anurag Anshu, Nikolas P. Breuckmann, Chinmay Nirkhe, "NLTS Hamiltonians from good quantum codes", STOC (2023); arXiv:2206.13228.
