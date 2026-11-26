# A multiply controlled NOT from Toffoli gates with one borrowed qubit

Let $n \ge 7$ and let $\wedge_{n-2}(X)$ be the gate on $n - 1$ of $n$ qubits that flips the target exactly when its $n - 2$
controls are all $|1\rangle$. On $n$ qubits, $\wedge_{n-2}(X)$ is a product of $8(n - 5)$ Toffoli gates $\wedge_2(X)$, using
the remaining qubit as a work qubit whose state is arbitrary and is restored; consequently it is a product of at most
$48n - 204$ single-qubit gates and CNOTs. The construction splits the controls into two groups of sizes
$m_1 = \lceil n/2 \rceil$ and $m_2 = n - m_1 - 1$, simulates $\wedge_{m_1}(X)$ and $\wedge_{m_2}(X)$ by $4(m - 2)$ Toffoli
gates each using the idle qubits as work qubits, and composes two of each with the borrowed qubit as an intermediate
target.

## Depends on

- [A doubly controlled unitary from controlled square roots](doubly-controlled-unitary-from-a-square-root.md)

## Proof depends on

- [A doubly controlled unitary from controlled square roots](doubly-controlled-unitary-from-a-square-root.md)

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467, arXiv:quant-ph/9503016, Section 7.1, Lemma 7.2 ($\wedge_m(\sigma_x)$ from $4(m - 2)$ Toffoli gates), Lemma 7.3 (two $\wedge_m$ and two $\wedge_{n-m-1}$ gates) and Corollary 7.4 ("$8(n - 5)$ $\wedge_2(\sigma_x)$ gates ... as well as by $48n - 204$ basic operations").
