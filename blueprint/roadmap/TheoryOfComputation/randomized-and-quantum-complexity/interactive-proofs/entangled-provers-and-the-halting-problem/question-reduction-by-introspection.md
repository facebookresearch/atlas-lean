# Question reduction by introspection

There is a polynomial-time transformation mapping a $\lambda$-bounded normal form verifier $\mathcal{V} = (S, D)$ (sampler time $T_S(n)$ and decider time $T_D(n)$ at most $n^\lambda$) to a normal form verifier $\mathcal{V}^{\mathrm{intro}}$ whose questions at index $n$ have length $\mathrm{poly}(n, \lambda)$ (polylogarithmic in $N = 2^n$) and whose decider runs in time $\mathrm{poly}(T_S(N), T_D(N))$, with constants $a, b > 0$ such that (Ji–Natarajan–Vidick–Wright–Yuen, Theorem 8.3):

- *(Completeness)* if $\mathcal{V}_{2^n}$ has a value-$1$ projective, consistent, commuting (PCC) strategy, then so does $\mathcal{V}^{\mathrm{intro}}_n$;
- *(Soundness)* for every $\varepsilon > 0$, if $\omega^*(\mathcal{V}^{\mathrm{intro}}_n) > 1 - \varepsilon$, then $\omega^*(\mathcal{V}_{2^n}) \ge 1 - \delta(\varepsilon, n)$ where $\delta(\varepsilon, n) = a\bigl((\lambda n)^a \varepsilon^b + (\lambda n)^{-b}\bigr)$; in particular, $\omega^*(\mathcal{V}_{2^n}) \le 1/2$ implies $\omega^*(\mathcal{V}^{\mathrm{intro}}_n) \le 1 - \varepsilon(n)$ for an inverse-polynomial gap $\varepsilon(n) = 1/\mathrm{poly}(\lambda n)$.

## Proof sketch

Instead of sending the provers their questions, the verifier commands them to sample the questions themselves by measuring shared EPR pairs in a basis prescribed by the conditionally linear structure of the sampler. The Pauli basis test certifies that the provers' measurements are the honest Pauli measurements, so the self-sampled questions are distributed correctly and cannot be adapted by a cheating prover. Conditional linearity is what makes the two provers' samples jointly simulable by local Pauli measurements.

## Depends on

- [Conditionally linear question distributions](conditionally-linear-question-distributions.md)
- [Synchronous two-prover games](synchronous-two-prover-games.md)
- [Uniformly generated families of two-prover one-round games](uniformly-generated-game-families.md)

## Proof depends on

- [Pauli basis test with polylogarithmic question length](introspectable-pauli-basis-test.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
