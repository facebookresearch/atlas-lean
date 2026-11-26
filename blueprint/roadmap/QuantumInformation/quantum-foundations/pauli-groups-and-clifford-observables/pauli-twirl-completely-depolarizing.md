# The Pauli twirl is completely depolarizing

For every matrix $\rho$ on $n$ qubits,

$$
\sum_{a,b\in\{0,1\}^n}X^aZ^b\,\rho\,(X^aZ^b)^* = 2^n\operatorname{Tr}(\rho)\,I .
$$

With a reference system, for $\rho$ on $\mathbb{C}^{\{0,1\}^n}\otimes\mathbb{C}^\kappa$: $\sum_{a,b}(X^aZ^b\otimes I)\rho(X^aZ^b\otimes I)^* = 2^n\,I\otimes\operatorname{Tr}_A\rho$, a product state, so all correlations with the reference are erased (the quantum one-time pad).

## Proof sketch

Summing over $b$ first multiplies the $(u,u')$ entry by $\sum_b(-1)^{b\cdot(u+u')} = 2^n[u=u']$, killing off-diagonal entries. Summing the remaining diagonal over the shifts $X^a$ replaces each diagonal entry by the trace. The reference version is the same computation blockwise.

## Depends on

- [Pauli strings and the Pauli group modulo $i$ as a Heisenberg group](pauli-group-modulo-i.md)
- [Density matrices, pure states and reduced states](../../quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)

## Sources

- R. de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
