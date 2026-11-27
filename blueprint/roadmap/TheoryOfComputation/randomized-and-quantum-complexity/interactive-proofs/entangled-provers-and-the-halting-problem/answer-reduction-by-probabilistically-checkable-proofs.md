# Answer reduction through oracularization and probabilistically checkable proofs

There is a polynomial-time transformation mapping a $\lambda$-bounded normal form verifier $\mathcal{V}$ with question length $q(n)$ and decider time $T_D(n)$ (controlled by $\lambda$ and the verifier level) to a normal form verifier $\mathcal{V}^{\mathrm{AR}}$ with question length $\mathrm{poly}(q(n), \log T_D(n))$, answer length $\mathrm{polylog}(T_D(n))$, and decider time $\mathrm{poly}(q(n), \log T_D(n))$ (more precisely bounded in terms of $\lambda$, $\mu$, $\sigma$, and the level in Theorem 10.30) that preserves value-$1$ PCC strategies and satisfies the inverse-polynomial soundness bound (Ji–Natarajan–Vidick–Wright–Yuen, arXiv:2001.04383v4, Theorem 10.30): if $\omega^*(\mathcal{V}^{\mathrm{AR}}_n) > 1 - \varepsilon$, then $\omega^*(\mathcal{V}_n) \ge 1 - \delta(\varepsilon, n)$ where $\delta(\varepsilon, n) = \sigma^a (\lambda n)^{\mu a} \varepsilon^b + (\lambda n)^{-\mu b}$ (so whenever $\varepsilon_1(n) \ge 2(\lambda n)^{-\mu b}$, choosing $\mu$ to match $\varepsilon_1$ yields an inverse-polynomial $\varepsilon_2(n)$ with $\delta(\varepsilon_2, n) < \varepsilon_1(n)$, hence $\omega^*(\mathcal{V}_n) \le 1 - \varepsilon_1(n)$ implies $\omega^*(\mathcal{V}^{\mathrm{AR}}_n) \le 1 - \varepsilon_2(n)$).

## Proof sketch

Oracularization lets one prover receive both questions and return both answers, so the decision predicate becomes a function of a single answer string. The provers are then asked to encode a probabilistically checkable proof of proximity that the decider accepts, and the verifier reads only a constant number of locations, tested by a low-degree test whose quantum soundness controls entangled cheating. Composition with the PCP theorem shrinks the decision time to polylogarithmic.

## Depends on

- [Conditionally linear question distributions](conditionally-linear-question-distributions.md)
- [Synchronous two-prover games](synchronous-two-prover-games.md)

## Proof depends on

- [Question reduction by introspection](question-reduction-by-introspection.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../../../pcp-and-inapproximability/pcp-theorem.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
- Anand Natarajan, John Wright, "NEEXP is contained in MIP*", FOCS (2019); arXiv:1904.05870.
