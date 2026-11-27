# The Pauli twirl of a channel is a Pauli channel

Let $\Lambda$ be a [quantum channel](../../quantum-operations/quantum-channel.md) on $n$ qubits with Kraus operators
$A_l$, $\Lambda(\rho) = \sum_l A_l \rho A_l^{*}$, and expand $A_l = \sum_P \alpha_{l, P}\, P$ in the
[Pauli basis](../stabilizer-formalism/pauli-expansion-of-a-matrix.md) $\{I, X, Y, Z\}^{\otimes n}$. The
*Pauli twirl* of $\Lambda$ averages its conjugates by all $4^n$ Pauli products:

$$\Lambda_{\mathrm{tw}}(\rho) = \frac{1}{4^n} \sum_{Q} Q\, \Lambda(Q \rho Q)\, Q = \sum_{P} p_P\, P \rho P,
\qquad p_P = \sum_l |\alpha_{l, P}|^2 .$$

So the twirl is a Pauli channel: the probabilities $p_P$ are nonnegative and sum to $1$ by trace preservation, and the
cross terms $P \rho P'$ with $P \ne P'$ cancel because $Q P Q = (-1)^{\omega(P, Q)} P$, so such a term picks up the sign
$(-1)^{\omega(P, Q) + \omega(P', Q)}$, which averages to zero over $Q$ unless $P = P'$, where $\omega$ is the
[symplectic product](../stabilizer-formalism/symplectic-product-of-pauli-operators.md).

## Depends on

- [Every matrix is a combination of Pauli operators](../stabilizer-formalism/pauli-expansion-of-a-matrix.md)
- [Quantum channel](../../quantum-operations/quantum-channel.md)
- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md)

## Proof depends on

- [Pauli operators are orthogonal for the trace inner product](../stabilizer-formalism/pauli-operators-form-an-orthogonal-basis.md)
- [Pauli operators commute exactly when their symplectic product vanishes](../stabilizer-formalism/pauli-operators-commute-iff-symplectic-product-vanishes.md)

## Sources

- C. Dankert, R. Cleve, J. Emerson and E. Livine, *Exact and approximate unitary 2-designs and their application to fidelity estimation*, Phys. Rev. A 80 (2009), 012304, arXiv:quant-ph/0606161, equation (7) (the $\mu$-twirl $\Lambda \mapsto \int d\mu(U)\, U^\dagger \Lambda(U X U^\dagger) U$) and the computation before equation (10): a $P_n$-twirl of $X \mapsto A X B$ is $X \mapsto \sum_a \alpha_a \beta_a P_a X P_a$, using the symplectic inner product; Theorem 1 (the Clifford group is a unitary 2-design).
