# A doubly controlled unitary from controlled square roots

Let $U$ be a unitary $2 \times 2$ matrix, let $V$ be a unitary with $V^2 = U$, and let $\wedge_2(U)$ be the three-qubit
gate applying $U$ to qubit $3$ exactly when qubits $1$ and $2$ are both $|1\rangle$. Then $\wedge_2(U)$ equals the
product, in this order, of $\wedge_1(V)$ with control $2$ and target $3$, a CNOT from qubit $1$ to qubit $2$,
$\wedge_1(V^{*})$ with control $2$ and target $3$, a CNOT from qubit $1$ to qubit $2$, and $\wedge_1(V)$ with control $1$
and target $3$. Indeed on the basis state with control bits $x_1, x_2$ the target receives
$V^{x_2} (V^{*})^{x_1 \oplus x_2} V^{x_1}$, which is $I$ unless $x_1 = x_2 = 1$, when it is $V^2 = U$. By the
[two-CNOT construction](controlled-unitary-from-two-cnots-and-single-qubit-gates.md) each $\wedge_1$ gate is a product of
at most six gates, so $\wedge_2(U)$ is a product of at most $20$ single-qubit gates and CNOTs; the Toffoli gate is the case
$U = X$.

## Depends on

- [A controlled single-qubit unitary from two CNOTs and four single-qubit gates](controlled-unitary-from-two-cnots-and-single-qubit-gates.md)

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467, arXiv:quant-ph/9503016, Section 6, Lemma 6.1 and the table of conditions after it.
