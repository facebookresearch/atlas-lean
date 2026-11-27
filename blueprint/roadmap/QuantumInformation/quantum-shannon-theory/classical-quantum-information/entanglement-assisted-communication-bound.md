# Entanglement-assisted classical communication bound (optimality of superdense coding)

Let Alice and Bob share a density matrix $\sigma$ on $\mathbb{C}^{\iota_0}\otimes\mathbb{C}^\kappa$. To send $x$ drawn from a distribution $p$ on a finite set $X$, Alice applies a channel $K_x$ from $\mathbb{C}^{\iota_0}$ to $\mathbb{C}^\iota$ (given by Kraus operators) to her share and sends the resulting register to Bob. Then the ensemble $\tau_x = (K_x\otimes\mathrm{id})(\sigma)$ on $\mathbb{C}^\iota\otimes\mathbb{C}^\kappa$ satisfies $\chi(p,\tau)\le 2\log_2|\iota|$, independent of $\iota_0$ and $\kappa$. Hence for every POVM measurement by Bob on $\mathbb{C}^\iota\otimes\mathbb{C}^\kappa$ with outcome $Y$, the classical mutual information satisfies $I(X:Y)\le 2\log_2|\iota|$ bits; sending $n$ qubits conveys at most $2n$ bits even with prior entanglement, and without entanglement at most $\log_2|\iota|$ bits.

## Proof sketch

Write $A$ for the sent register and $B$ for Bob's share. By no-signalling every $\tau_x$ has the same $B$-marginal $\sigma_B$. Subadditivity gives $S(\bar\tau_{AB}) \le \log_2|\iota| + S(\sigma_B)$, and Araki-Lieb gives $S(\tau_{x,AB}) \ge S(\sigma_B) - \log_2|\iota|$; subtracting yields $\chi\le 2\log_2|\iota|$. Holevo's theorem converts the bound on $\chi$ into a bound on accessible mutual information.

## Depends on

- [Von Neumann entropy and Holevo information](von-neumann-entropy-and-holevo-information.md)
- [Superdense coding](../../quantum-foundations/superdense-coding.md)
- [Positive-operator-valued measurements and the Born rule](../../quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)

## Proof depends on

- [Basic properties of von Neumann entropy: bounds, additivity, subadditivity and Araki-Lieb](von-neumann-entropy-properties.md)
- [No-signalling for local operations](../../quantum-foundations/no-signalling-for-local-operations.md)
- [Holevo's theorem](../holevo-s-theorem.md)

## Sources

- R. de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
- A. S. Holevo, "Bounds for the quantity of information transmitted by a quantum communication channel", Problems of Information Transmission 9:177-183, 1973.
