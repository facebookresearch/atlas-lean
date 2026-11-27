# Tensor-stable positivity on the matrix multiplication state is undecidable

No algorithm decides, given a linear map on $3^2 \times 3^2$ matrices with rational Choi matrix, whether every tensor power of the map sends the projector onto the matrix multiplication state to a positive semidefinite matrix.

**Matrix multiplication state.** For $d, n \geq 1$ let

$$
\lvert\chi_n\rangle = \sum_{i_1, \dots, i_n = 1}^{d} \lvert i_1, i_2\rangle \otimes \lvert i_2, i_3\rangle \otimes \cdots \otimes \lvert i_n, i_1\rangle \in (\mathbb{C}^{d} \otimes \mathbb{C}^{d})^{\otimes n},
$$

a ring of $n$ maximally entangled pairs of dimension $d$ shared between neighboring sites, and $\chi_n = \lvert\chi_n\rangle\langle\chi_n\rvert$.

**Problem.** Given $d \in \mathbb{N}$ and a linear map $\mathcal{P} : \mathcal{M}_{d^2} \to \mathcal{M}_{d^2}$ whose [Choi matrix](../../../Analysis/not-yet-classified/choi/choi-matrix.md) has rational entries, is $\mathcal{P}^{\otimes n}(\chi_n)$ positive semidefinite for all $n \geq 1$?

**Theorem (van der Eyden, Netzer and De las Cuevas).** This problem is undecidable, even for $d = 3$.

A map is *tensor stable positive* if $\mathcal{P}^{\otimes n}$ is a positive map for every $n$; every such map answers the problem positively, but a positive answer does not imply tensor stable positivity, because only the input $\chi_n$ is tested. Whether tensor stable positivity itself is decidable is left open in the source, which conjectures that it is not.

## Depends on

- [Choi matrix of a complex-linear matrix map](../../../Analysis/not-yet-classified/choi/choi-matrix.md)
- [Bell basis and maximally entangled states](../../../QuantumInformation/quantum-foundations/bell-basis-and-maximally-entangled-states.md)

## Proof depends on

- [Positivity of a translation-invariant MPDO for all system sizes is undecidable](../../quantum-states-distances-and-entropy/tensor-network-states/positivity-of-translation-invariant-mpdos.md)

## Expansion

The proof reduces the positivity problem for translation-invariant diagonal matrix product density operators, $\tau_n(C) = \sum_{i_1, \dots, i_n} \operatorname{tr}(C_{i_1} \cdots C_{i_n}) \lvert i_1 \cdots i_n\rangle\langle i_1 \cdots i_n\rvert$, with rational $9 \times 9$ matrices $C_1, \dots, C_9$. The source quotes this problem as undecidable from De las Cuevas, Cubitt, Cirac, Wolf and Pérez-García. From $C$ it builds a map $\mathcal{P}$ on $\mathcal{M}_9$ whose tensor powers, applied to the ring of maximally entangled pairs, contract the virtual indices of $\chi_n$ exactly as the trace in $\tau_n(C)$ does. Then $\mathcal{P}^{\otimes n}(\chi_n)$ is positive semidefinite exactly when $\tau_n(C)$ is. Since the Choi matrix may be scaled by a positive integer, the problem is equally undecidable for integer Choi matrices.

## Sources

- M. van der Eyden, T. Netzer and G. De las Cuevas, "Halos and undecidability of tensor stable positive maps", *Journal of Physics A: Mathematical and Theoretical* 55(26), 264006, 2022, doi:[10.1088/1751-8121/ac726e](https://doi.org/10.1088/1751-8121/ac726e). Numbering of the version read, arXiv:2110.02113v2: Problem 14 (the decision problem on the matrix multiplication state), Theorem 15 (its undecidability for $d = 3$) and its proof, Problem 16 and Theorem 17 (the positivity problem it reduces from, quoted as undecidable already for $s = t = 7$), Equation (1) (the matrix multiplication state), and Problem 18 and Conjecture 21 (tensor stable positivity and its conjectured undecidability).
