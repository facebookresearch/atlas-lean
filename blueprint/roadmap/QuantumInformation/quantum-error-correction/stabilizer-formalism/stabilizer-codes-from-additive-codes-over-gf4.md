# Stabilizer codes from additive codes over GF(4)

Let $\mathrm{GF}(4) = \{0, 1, \omega, \bar\omega\}$ with $\omega^2 = \omega + 1$, conjugation $\bar x = x^2$ and trace
$\operatorname{Tr} x = x + \bar x \in \mathbb{F}_2$. Map $(a, b) \in \mathbb{F}_2^{2n}$ to
$\phi(a, b) = \omega a + \bar\omega b \in \mathrm{GF}(4)^n$, and define the trace inner product
$u * v = \sum_{j} \operatorname{Tr}(u_j \bar v_j)$. Then

$$\phi(v) * \phi(v') = \omega(v, v'), \qquad \operatorname{wt}(\phi(a, b)) = \#\{i : (a_i, b_i) \ne (0, 0)\},$$

so $\phi$ carries the [symplectic product](symplectic-product-of-pauli-operators.md) to the trace inner product and the
[weight of a Pauli operator](../distance-of-a-quantum-code/pauli-weight.md) to the Hamming weight.

Let $C \subseteq \mathrm{GF}(4)^n$ be additive (closed under addition) with $2^{n-k}$ elements, $k \ge 1$, such that
$C \subseteq C^{\perp}$ for the trace inner product and $C^{\perp} \setminus C$ contains no vector of weight at most
$d - 1$. Then there is a stabilizer group $S$ whose vectors $(a, b)$ form $\phi^{-1}(C)$: take a basis
$v_1, \dots, v_{n-k}$ of $\phi^{-1}(C)$ over $\mathbb{F}_2$ and the Hermitian Pauli operators
$g_j = i^{a_j \cdot b_j} X^{a_j} Z^{b_j}$ for $v_j = (a_j, b_j)$; they commute because $C \subseteq C^{\perp}$, and no nonempty
product of them is a scalar because the $v_j$ are linearly independent, so they generate a stabilizer group $S$ with
$-I \notin S$. The code space of $S$ has dimension $2^k$ and [distance at least $d$](../distance-of-a-quantum-code/has-distance-at-least.md): it is an
$[[n, k, d']]$ code with $d' \ge d$.

The condition $C \subseteq C^{\perp}$ is commutativity of $S$, and $C^{\perp}$ corresponds to the normalizer, so this is
the [correctability criterion](../stabilizer-codes-correctability-criterion-and-distance.md) restated over
$\mathrm{GF}(4)$; Calderbank, Rains, Shor and Sloane state it with $|C| = 2^k$ and parameters $[[n, n - k, d]]$.

## Depends on

- [Symplectic product of Pauli operators](symplectic-product-of-pauli-operators.md)
- [Pauli group, Clifford group and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-clifford-group-and-stabilizer-states.md)
- [Distance of a quantum code (lower bound)](../distance-of-a-quantum-code/has-distance-at-least.md)
- [Weight of a Pauli operator](../distance-of-a-quantum-code/pauli-weight.md)

## Proof depends on

- [Stabilizer codes: correctability criterion and distance](../stabilizer-codes-correctability-criterion-and-distance.md)
- [Dimension of a stabilizer code](../stabilizer-codes/finrank-stabilizer-code.md)

## Sources

- A. R. Calderbank, E. M. Rains, P. W. Shor and N. J. A. Sloane, *Quantum error correction via codes over GF(4)*, IEEE Trans. Inform. Theory 44 (1998), 1369–1387, arXiv:quant-ph/9608006, Section 2, Theorem 1, and Section 3, Theorem 2 and the identity before equation (4).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.4, equation (3.28).
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.13.
