# Quantum channel

For nonempty finite index sets $\Sigma$ and $\Gamma$, a linear map $\Phi$ from complex $\Sigma \times \Sigma$ matrices to complex
$\Gamma \times \Gamma$ matrices underlies a *quantum channel* exactly when it is completely positive, meaning that
$\Phi \otimes \mathrm{id}_{M_Z(\mathbb{C})}$ maps positive semidefinite matrices to positive semidefinite matrices for every finite
index set $Z$, and trace preserving, meaning that $\operatorname{Tr} \Phi(X) = \operatorname{Tr} X$ for every $X$. Examples are the
unitary channel $\rho \mapsto U \rho U^{*}$, the partial trace, the preparation of a fixed state, and the Pauli channel
$\rho \mapsto \sum_{P} p_P\, P \rho P^{*}$ over Pauli operators $P$ with probabilities $p_P$ (for the Hermitian tensor products of
$I, X, Y, Z$ this is $P \rho P$; for $P = iI$ the map $\rho \mapsto P \rho P = -\rho$ is not a channel).

## Sources

- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8 (2019); also *Quantum Information Theory*, 2nd ed., Cambridge University Press, 2017, Section 4.4, Definitions 4.4.2 (completely positive map) and 4.4.3 (quantum channel), Criteria 4.4.1–4.4.3.
