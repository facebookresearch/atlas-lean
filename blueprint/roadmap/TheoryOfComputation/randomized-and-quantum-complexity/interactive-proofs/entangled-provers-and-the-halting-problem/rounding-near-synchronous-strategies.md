# Near-optimal strategies of synchronous games are close to synchronous ones

Let $G$ be a synchronous game and $\kappa := \min_{x : \mu_A(x) > 0} \mu(x, x) / \mu_A(x) > 0$. If a finite-dimensional strategy for $G$ has value at least $1 - \varepsilon$, then there is a synchronous strategy (projections $P^x_a$ on some $\mathbb{C}^{d'}$, evaluated against the normalized trace) whose value is at least $1 - \delta$, where $\delta = \mathrm{poly}(\varepsilon / \kappa)$ depends polynomially on $\varepsilon/\kappa$ and not on the number of questions or answers. In particular $\omega^*(G) = 1$ if and only if $\omega^*_s(G) = 1$.

## Proof sketch

Near-perfect consistency on diagonal questions forces $\langle \psi | A^x_a \otimes \overline{B^x_a} | \psi \rangle$ to be close to $\langle \psi | A^x_a \otimes I | \psi \rangle$ summed over $a$. Writing $\psi$ through its Schmidt decomposition as $\sqrt{\sigma}$ for a density matrix $\sigma$, this says that the operators $A^x_a$ almost commute with $\sqrt\sigma$ in the $\sigma$-weighted Hilbert-Schmidt norm. A spectral truncation of $\sigma$ into level sets, followed by orthogonalization of the measurements on each level set, yields projective measurements evaluated against a normalized trace whose correlations differ by $\mathrm{poly}(\varepsilon/\kappa)$.

## Depends on

- [Synchronous two-prover games](synchronous-two-prover-games.md)
- [Uniformly generated families of two-prover one-round games](uniformly-generated-game-families.md)

## Sources

- Thomas Vidick, "Almost synchronous quantum correlations", Journal of Mathematical Physics 63 (2022); arXiv:2103.02468.
- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
