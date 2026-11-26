# Dimension-free fidelity estimation and local observables from classical shadows

(i) With Clifford shadows, the fidelities $\langle\psi_i|\rho|\psi_i\rangle$ with $M$ arbitrary pure states are estimated to accuracy $\varepsilon$ from $O(\log(M/\delta)/\varepsilon^2)$ snapshots, independently of the number of qubits $n$. (ii) With Pauli shadows, the expectations of $M$ observables each acting on at most $k$ qubits with $\|O_i\|_\infty \le 1$ are estimated from $O(4^k \log(M/\delta)/\varepsilon^2)$ snapshots.

## Proof sketch

Apply the main theorem with the shadow norm bounds: $\mathrm{Tr}(O_0^2) \le 1$ for $O = |\psi\rangle\langle\psi|$ gives a constant Clifford shadow norm, and $k$-local observables have Pauli shadow norm at most $2^k$.

## Depends on

- [Classical shadows from randomized measurements](randomized-measurement-classical-shadow.md)

## Proof depends on

- [Huang-Kueng-Preskill: classical shadows predict many properties from few measurements](classical-shadows-predict-many-observables.md)
- [Variance bound for single-snapshot estimators](variance-of-classical-shadow-estimators.md)

## Sources

- Hsin-Yuan Huang, Richard Kueng, John Preskill, "Predicting many properties of a quantum system from very few measurements", Nature Physics 16 (2020); arXiv:2002.08953.
