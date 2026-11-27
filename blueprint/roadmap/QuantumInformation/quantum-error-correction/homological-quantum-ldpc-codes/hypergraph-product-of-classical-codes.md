# Hypergraph product of two classical codes (Tillich-Zemor)

Let $H_1 \in \mathbb{F}_2^{m_1 \times n_1}$ and $H_2 \in \mathbb{F}_2^{m_2 \times n_2}$ be parity-check matrices. Their *hypergraph product* is the CSS code on $n = n_1 n_2 + m_1 m_2$ qubits with

$$
H_X = \big( H_1 \otimes I_{n_2} \ \big|\ I_{m_1} \otimes H_2^{T} \big), \qquad H_Z = \big( I_{n_1} \otimes H_2 \ \big|\ H_1^{T} \otimes I_{m_2} \big).
$$

It is the CSS code of the tensor product of the two-term complexes $\mathbb{F}_2^{n_1} \xrightarrow{H_1} \mathbb{F}_2^{m_1}$ and $\mathbb{F}_2^{m_2} \xrightarrow{H_2^T} \mathbb{F}_2^{n_2}$ (suitably indexed).

## Depends on

- [The CSS code of a chain complex](css-code-of-a-chain-complex.md)
- [Linear code](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md)

## Sources

- Jean-Pierre Tillich, Gilles Zemor, "Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength", IEEE Transactions on Information Theory 60(2) (2014); arXiv:0903.0566.
