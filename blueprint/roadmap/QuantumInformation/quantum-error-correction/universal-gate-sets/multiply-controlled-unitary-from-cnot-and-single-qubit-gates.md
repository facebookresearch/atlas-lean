# Multiply controlled unitaries from CNOT and single-qubit gates

Let $U$ be a unitary $2 \times 2$ matrix and $m \ge 1$, and let $\wedge_m(U)$ be the gate on $m + 1$ qubits that applies $U$
to the last qubit exactly when the first $m$ qubits are all $|1\rangle$. Then $\wedge_m(U)$ is a product of $\Theta(m^2)$
single-qubit gates and CNOTs acting on these $m + 1$ qubits only, with no ancilla qubits; Barenco et al. count
$48 (m+1)^2 + O(m)$ gates.

The recursion: with $n = m + 1$ and a unitary $V$ with $V^2 = U$, $\wedge_{n-1}(U)$ equals $\wedge_1(V)$ controlled by
qubit $n - 1$, then $\wedge_{n-2}(X)$ from qubits $1, \dots, n-2$ onto qubit $n - 1$, then $\wedge_1(V^{*})$ controlled by
qubit $n - 1$, then the same $\wedge_{n-2}(X)$, then $\wedge_{n-2}(V)$ controlled by qubits $1, \dots, n-2$, all
$\wedge(V)$ gates targeting qubit $n$. The target receives $V^{y} (V^{*})^{y \oplus c} V^{c}$, where $c$ is the AND of the
first $n - 2$ bits and $y$ is bit $n - 1$, which is $U$ if $c = y = 1$ and $I$ otherwise. The two $\wedge_{n-2}(X)$ gates cost
$O(n)$ each, by the [Toffoli chain with a borrowed qubit](multiply-controlled-not-with-one-borrowed-qubit.md) using
qubit $n$, so the cost satisfies $C_{n-1} = C_{n-2} + \Theta(n)$.

## Depends on

- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Proof depends on

- [A controlled single-qubit unitary from two CNOTs and four single-qubit gates](controlled-unitary-from-two-cnots-and-single-qubit-gates.md)
- [A doubly controlled unitary from controlled square roots](doubly-controlled-unitary-from-a-square-root.md)
- [A multiply controlled NOT from Toffoli gates with one borrowed qubit](multiply-controlled-not-with-one-borrowed-qubit.md)

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467, arXiv:quant-ph/9503016, Section 7.2, Lemma 7.5 (the network with $V^2 = U$) and Corollary 7.6 ($\Theta(n^2)$ basic operations, "$48 n^2 + O(n)$").
