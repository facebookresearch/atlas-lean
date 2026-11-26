# Answer reduction through oracularization and probabilistically checkable proofs

There is a polynomial-time transformation mapping a normal form verifier with question length $q(n)$ and decider time $T_D(n)$ to a normal form verifier with question length $\mathrm{poly}(q(n), \log T_D(n))$, answer length $\mathrm{polylog}(T_D(n))$ and decider time $\mathrm{poly}(q(n), \log T_D(n))$ that preserves value $1$ (for oracularizable synchronous strategies) and maps value at most $1 - c$ to value at most $1 - c'$ for constants $c, c' > 0$.

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
