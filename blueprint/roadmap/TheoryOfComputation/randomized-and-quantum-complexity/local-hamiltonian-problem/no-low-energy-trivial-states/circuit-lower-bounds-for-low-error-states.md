# Anshu-Nirkhe: circuit lower bounds for low-energy states of code Hamiltonians

Let $C$ be an $[[n, k, d]]$ stabilizer code defined by checks $C_1, \dots, C_N$ of constant locality $\ell = O(1)$ (every check acts nontrivially on at most $\ell$ qubits and every qubit lies in at most $\ell$ checks), and let $H = \sum_{i=1}^{N} (I - C_i)/2$ be its code Hamiltonian. For every $\varepsilon$ in the small-positive-energy regime $0 < \varepsilon < 1$ (so that $\log(1/\varepsilon) > 0$), every $n$-qubit state $\psi$ with $\mathrm{Tr}(H\psi) \le \varepsilon n$ has circuit depth

$$
\Omega\!\left( \min\left\{ \log d,\ \log \frac{k + d}{n\sqrt{\varepsilon \log(1/\varepsilon)}} \right\} \right).
$$

In particular, for codes of linear rate and distance $n^{\Omega(1)}$ (for instance hypergraph product codes of good classical LDPC codes), for every fixed $\delta > 0$ every state of energy $O(n^{1-\delta})$ has circuit depth $\Omega(\delta \log n)$.

## Proof sketch

An entropic argument shows that states of circuit depth at most $\log d$ are far in $\ell_1$ distance from the code space of a code of high rate. To pass from the code space to low-energy states, the syndrome is measured by a constant-depth circuit, which exists because the checks have constant locality, and one uses that every eigenspace of a stabilizer code Hamiltonian is locally indistinguishable: reduced states on fewer than $d$ qubits do not depend on the state within the eigenspace.

## Depends on

- [Stabilizer codes: correctability criterion and distance](../../../../QuantumInformation/quantum-error-correction/stabilizer-codes-correctability-criterion-and-distance.md)
- [Circuit depth of a quantum state and trivial states](trivial-states-of-bounded-circuit-depth.md)

## Sources

- Anurag Anshu, Chinmay Nirkhe, "Circuit lower bounds for low-energy states of quantum code Hamiltonians", ITCS (2022), doi:10.4230/LIPIcs.ITCS.2022.6; arXiv:2011.02044 (Theorem 1, Eq. (1)).
