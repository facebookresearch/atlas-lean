# The quantum MacWilliams identity

Let $\mathcal{E}_d$ be the set of $n$-qubit Pauli products $\sigma_1 \otimes \cdots \otimes \sigma_n$,
$\sigma_j \in \{I, X, Y, Z\}$, with exactly $d$ non-identity factors. For Hermitian operators $O_1, O_2$ on $n$ qubits with
$\operatorname{Tr} O_1, \operatorname{Tr} O_2, \operatorname{Tr}(O_1 O_2)$ nonzero define

$$A_d = \frac{1}{\operatorname{Tr} O_1 \operatorname{Tr} O_2} \sum_{E \in \mathcal{E}_d} \operatorname{Tr}(E O_1) \operatorname{Tr}(E^{*} O_2), \qquad
B_d = \frac{1}{\operatorname{Tr}(O_1 O_2)} \sum_{E \in \mathcal{E}_d} \operatorname{Tr}(E O_1 E^{*} O_2),$$

and the weight enumerators $A(z) = \sum_{d=0}^n A_d z^d$, $B(z) = \sum_{d=0}^n B_d z^d$. Then

$$B(z) = \frac{\operatorname{Tr} O_1 \operatorname{Tr} O_2}{2^n \operatorname{Tr}(O_1 O_2)}\, (1 + 3z)^n\, A\Big( \frac{1 - z}{1 + 3z} \Big).$$

Taking $O_1 = O_2$ the projector onto a code gives nonnegative coefficients $A_d$, $B_d$ that, with linear programming,
rule out codes: Shor and Laflamme show there is no degenerate $[[5, 1, 3]]$ code and no $[[9, 1, 5]]$ code. The identity is
the analogue of the [MacWilliams identity](../../../InformationTheory/error-correcting-codes/macwilliams-identity.md) for
codes over $\mathrm{GF}(4)$.

## Depends on

- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md)

## Proof depends on

- [Pauli operators are orthogonal for the trace inner product](../stabilizer-formalism/pauli-operators-form-an-orthogonal-basis.md)
- [Every matrix is a combination of Pauli operators](../stabilizer-formalism/pauli-expansion-of-a-matrix.md)

## Related topics

- [MacWilliams identity](../../../InformationTheory/error-correcting-codes/macwilliams-identity.md): the classical identity

## Sources

- P. Shor and R. Laflamme, *Quantum analog of the MacWilliams identities for classical coding theory*, Phys. Rev. Lett. 78 (1997), 1600–1602, arXiv:quant-ph/9610040, equations (1)–(6) and the examples that follow.
