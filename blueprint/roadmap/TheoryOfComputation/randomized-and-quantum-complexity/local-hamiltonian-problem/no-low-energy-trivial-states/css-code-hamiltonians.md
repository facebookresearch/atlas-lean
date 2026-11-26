# CSS code Hamiltonians of quantum LDPC codes

Let $H_X \in \mathbb{F}_2^{m_X \times n}$ and $H_Z \in \mathbb{F}_2^{m_Z \times n}$ satisfy $H_X H_Z^{T} = 0$ and have row and column weights at most $w$. The associated *code Hamiltonian* is

$$
H = \sum_{r \text{ row of } H_X} \frac{I - X^{r}}{2} + \sum_{s \text{ row of } H_Z} \frac{I - Z^{s}}{2},
$$

where $X^r = \bigotimes_i X^{r_i}$. It is a commuting frustration-free $(w, 2w)$-local Hamiltonian whose ground space is the CSS code space; the energy of a computational-basis string $x$ under the $Z$-part equals the syndrome weight $|H_Z x|$.

## Depends on

- [Bounded-degree local Hamiltonian families and relative energy](normalized-local-hamiltonian-families-and-relative-energy.md)
- [CSS codeword](../../../../QuantumInformation/quantum-error-correction/css-codes/codeword.md)
- [Stabilizer codes: correctability criterion and distance](../../../../QuantumInformation/quantum-error-correction/stabilizer-codes-correctability-criterion-and-distance.md)

## Sources

- Anurag Anshu, Nikolas P. Breuckmann, Chinmay Nirkhe, "NLTS Hamiltonians from good quantum codes", STOC (2023); arXiv:2206.13228.
- Anurag Anshu, Chinmay Nirkhe, "Circuit lower bounds for low-energy states of quantum code Hamiltonians", ITCS (2022); arXiv:2011.02044.
