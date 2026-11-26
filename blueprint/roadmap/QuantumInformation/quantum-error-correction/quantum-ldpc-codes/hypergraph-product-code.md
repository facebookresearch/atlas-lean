# Hypergraph product code

Let $H_1 \in \mathbb{F}_2^{r_1 \times n_1}$ and $H_2 \in \mathbb{F}_2^{r_2 \times n_2}$ be parity-check matrices of
classical codes. Their *hypergraph product* is the CSS code on $n = n_1 n_2 + r_1 r_2$ qubits with

$$H_X = \big( H_1 \otimes I_{n_2} \ \big|\ I_{r_1} \otimes H_2^{T} \big), \qquad
H_Z = \big( I_{n_1} \otimes H_2 \ \big|\ H_1^{T} \otimes I_{r_2} \big),$$

which satisfy $H_X H_Z^{T} = H_1 \otimes H_2^{T} + H_1 \otimes H_2^{T} = 0$. It is the
[CSS code of the tensor product](css-code-of-a-chain-complex.md) of the two-term chain complexes defined by $H_1$ and
$H_2^{T}$, and in Tillich and Zémor's terms the code of the product of the Tanner graphs. If $H_1$ and $H_2$ have rows and
columns of bounded weight, so do $H_X$ and $H_Z$, so products of LDPC codes are [quantum LDPC](quantum-ldpc-code.md).
The hypergraph product of the parity-check matrices of two repetition codes, cyclic or not, gives the toric or the planar
surface code.

## Depends on

- [The CSS code of a chain complex](css-code-of-a-chain-complex.md)

## Sources

- J.-P. Tillich and G. Zémor, *Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength*, IEEE Trans. Inform. Theory 60 (2014), 1193–1202, arXiv:0903.0566, Section 3, Definition 3, and Section 4.3, Proposition 13.
- N. P. Breuckmann and J. N. Eberhardt, *Quantum low-density parity-check codes*, PRX Quantum 2 (2021), 040101, arXiv:2103.06309, Section IV.A and Appendix A.3 (the hypergraph product as a tensor product of chain complexes, Figure 6).
