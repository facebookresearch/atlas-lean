# Chen-Cotler-Huang-Li: shadow tomography without quantum memory needs many samples

For every $M$ there is a family of $M$ observables on $n$ qubits such that every protocol that measures the copies of an unknown state one at a time (with arbitrary adaptivity but without quantum memory across copies) and predicts all $M$ expectation values $\mathrm{tr}(O_x \rho)$ to error $\varepsilon$ with probability at least $2/3$ requires

$$
T = \Omega\Bigl( \frac{\min\{M/\log M,\ 2^n\}}{\varepsilon^2} \Bigr)
$$

copies. The family can be taken random: $O_i = U_i Z_n U_i^\dagger$ and $O_{i + M/2} = -O_i$ for $i \le M/2$, with $U_i$ independent Haar-random unitaries on $n$ qubits and $Z_n$ the Pauli-$Z$ operator on the last qubit, and the bound then holds with constant probability over the family. In contrast, protocols with quantum memory need only $\mathrm{poly}(n, \log M, 1/\varepsilon)$ copies.

## Proof sketch

Reduce to distinguishing the maximally mixed state from $\rho_x = 2^{-n}(I + 3\varepsilon O_x)$ for a uniformly random index $x$. Model a memoryless adaptive protocol as a tree of single-copy POVMs; a likelihood-ratio bound shows that any such protocol needs $\Omega\bigl(1/(\varepsilon^2 \delta)\bigr)$ copies, where $\delta = \sup_{|\phi\rangle} \frac{2}{M}\sum_{i \le M/2} \langle \phi | O_i | \phi \rangle^2$. For the random family, an $\epsilon$-net over pure states, concentration for Haar-random states and a union bound give $\delta = O(\log M / M) + 1/(2^n + 1)$ with constant probability. The separate bound for Pauli observables comes from a different family. Upper bounds with memory come from the Bădescu-O'Donnell algorithm.

## Depends on

- [The shadow tomography problem](shadow-tomography-problem.md)

## Proof depends on

- [Bădescu-O'Donnell: shadow tomography with log-squared dependence on the number of observables](improved-shadow-tomography-sample-complexity.md)

## Sources

- Sitan Chen, Jordan Cotler, Hsin-Yuan Huang, Jerry Li, "Exponential separations between learning with and without quantum memory", FOCS (2021); arXiv:2111.05881, Theorem 5.5, Lemma 5.6 and Corollary 5.7 (equation (110)).
