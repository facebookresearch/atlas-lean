# The class MIP* of languages with entangled two-prover proofs

For $0 \le s < c \le 1$, a language $L \subseteq \{0,1\}^*$ belongs to $\mathrm{MIP}^*_{c,s}$ if there is a uniformly generated family of two-prover one-round games $(G_z)_z$ such that

- (completeness) $z \in L$ implies $\omega^*(G_z) \ge c$;
- (soundness) $z \notin L$ implies $\omega^*(G_z) < s$.

Write $\mathrm{MIP}^* = \mathrm{MIP}^*_{1, 1/2}$. Here the verifier is classical and probabilistic, while the two non-communicating provers may share an arbitrary finite-dimensional entangled state and apply arbitrary local measurements.

## Depends on

- [Uniformly generated families of two-prover one-round games](uniformly-generated-game-families.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
- Joseph Fitzsimons, Zhengfeng Ji, Thomas Vidick, Henry Yuen, "Quantum proof systems for iterated exponential time, and beyond", STOC (2019); arXiv:1805.12166.
