# Quantum LDPC code

A family of [stabilizer codes](../distance-of-a-quantum-code/n-k-d-quantum-code.md) $[[n_i, k_i, d_i]]$ with
$n_i \to \infty$ is *low-density parity-check* (LDPC) if it has stabilizer generators such that the number of qubits on
which each generator acts and the number of generators acting on each qubit are both bounded by a constant independent
of $i$. For [CSS codes](css-code-of-a-chain-complex.md) this says that the rows and columns of $H_X$ and $H_Z$ have
bounded Hamming weight. The family is *good* if $k_i = \Theta(n_i)$ and $d_i = \Theta(n_i)$. Toric and surface codes are
LDPC with $k$ bounded and $d = \Theta(\sqrt{n})$; hypergraph product codes are LDPC with $k = \Theta(n)$ and
$d = \Theta(\sqrt{n})$.

## Depends on

- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)

## Sources

- N. P. Breuckmann and J. N. Eberhardt, *Quantum low-density parity-check codes*, PRX Quantum 2 (2021), 040101, arXiv:2103.06309, Section II.A.2 ("A low-density parity-check code (LDPC code) is a family of stabilizer codes such that the number of qubits participating in each check operator and the number of stabilizer checks that each qubit participates in are both bounded by a constant").
