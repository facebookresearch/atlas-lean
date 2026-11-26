# Logarithmic dependence on the number of observables is necessary

Any procedure, even with collective measurements on all copies, that predicts the fidelities of an unknown $n$-qubit state with $M$ given pure states to accuracy $\varepsilon$ with constant success probability requires $\Omega(\log(M)/\varepsilon^2)$ copies (for $M \le 2^{O(n)}$). Hence classical shadows are optimal up to constants for this task.

## Proof sketch

Choose $M$ nearly orthogonal pure states $\psi_1, \dots, \psi_M$ and let the unknown state be $\rho_i = (1 - 2\varepsilon)\frac{I}{2^n} + 2\varepsilon |\psi_i\rangle\langle\psi_i|$ for a uniformly random $i$. Accurate fidelity prediction identifies $i$, which requires $\log M$ bits of information. By Holevo's theorem the information extractable from $N$ copies is at most the Holevo quantity of the ensemble $\rho_i^{\otimes N}$, which is $O(N\varepsilon^2)$.

## Depends on

- [The shadow tomography problem](shadow-tomography-problem.md)
- [Holevo's theorem](../../quantum-shannon-theory/holevo-s-theorem.md)

## Proof depends on

- [The shadow tomography problem](shadow-tomography-problem.md)
- [Holevo's theorem](../../quantum-shannon-theory/holevo-s-theorem.md)

## Sources

- Hsin-Yuan Huang, Richard Kueng, John Preskill, "Predicting many properties of a quantum system from very few measurements", Nature Physics 16 (2020); arXiv:2002.08953.
