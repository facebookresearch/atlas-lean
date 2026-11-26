# Dimension of a hypergraph product code

Let the [hypergraph product](hypergraph-product-code.md) be built from $H_1 \in \mathbb{F}_2^{r_1 \times n_1}$ and
$H_2 \in \mathbb{F}_2^{r_2 \times n_2}$, and let $k_i = \dim \ker H_i$ and $k_i^{T} = \dim \ker H_i^{T}$ (the dimensions of
the code $C_i$ and of its transpose code $C_i^{T}$, with parity-check matrix $H_i^{T}$). Then the number of logical qubits
is

$$k = k_1 k_2 + k_1^{T} k_2^{T} .$$

In homological terms this is the Künneth formula for the tensor product of chain complexes. For full-rank $H_1, H_2$ the
transpose codes are trivial and $k = k_1 k_2$; with codes of positive rate this is $\Theta(n)$.

## Depends on

- [Hypergraph product code](hypergraph-product-code.md)

## Sources

- J.-P. Tillich and G. Zémor, *Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength*, IEEE Trans. Inform. Theory 60 (2014), 1193–1202, arXiv:0903.0566, Section 3, Proposition 14 and its proof.
- N. P. Breuckmann and J. N. Eberhardt, *Quantum low-density parity-check codes*, PRX Quantum 2 (2021), 040101, arXiv:2103.06309, Appendix A.3 (the Künneth formula).
