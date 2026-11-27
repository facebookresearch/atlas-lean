# Logarithmic dependence on the number of observables is necessary

Any procedure that measures the copies one at a time with a fixed sequence of POVMs, chosen before the $M$ pure states are revealed, and then predicts the fidelities of an unknown $n$-qubit state with all $M$ of them to accuracy $\varepsilon$ with high probability, requires $\Omega(\log(M)/\varepsilon^2)$ copies, provided $M \le \exp(2^n/32)$. Hence classical shadows are optimal up to constants among such procedures.

## Proof sketch

Turn the procedure into a communication protocol. Alice picks $i \in \{1, \dots, M\}$ uniformly and prepares copies of a state $\rho_i$ from an ensemble of $M$ states that the fidelities with $M$ pure states $\psi_1, \dots, \psi_M$ tell apart, so accurate prediction lets Bob recover $i$ and his data must carry $\log_2 M$ bits about $i$. Before the copies reach Bob, a Haar-random unitary $U$ rotates every copy to $U\rho_i U^\dagger$, and $U$ is revealed only after every copy has been measured; Bob then predicts the fidelities with the rotated states $U\psi_j$, which identify $i$ just as well. Because each POVM is fixed without knowledge of $U$, averaging over $U$ shows that each single-copy outcome carries only $O(\varepsilon^2)$ bits about $i$ given $U$, so $N\cdot O(\varepsilon^2) \ge \log_2 M$ and $N = \Omega(\log(M)/\varepsilon^2)$.

## Depends on

- [The shadow tomography problem](shadow-tomography-problem.md)

## Sources

- Hsin-Yuan Huang, Richard Kueng, John Preskill, "Predicting many properties of a quantum system from very few measurements", Nature Physics 16 (2020); arXiv:2002.08953.
