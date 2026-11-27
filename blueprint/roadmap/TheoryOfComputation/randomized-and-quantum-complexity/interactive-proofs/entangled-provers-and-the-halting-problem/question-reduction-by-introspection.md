# Question reduction by introspection

There is a polynomial-time transformation mapping a normal form verifier $\mathcal{V} = (S, D)$ whose sampler runs in time $T_S(n)$ to a normal form verifier $\mathcal{V}^{\mathrm{intro}}$ whose questions have length $\mathrm{polylog}(T_S(n))$ and whose decider runs in time $\mathrm{poly}(T_S(n), T_D(n))$, such that for every $n$:

- if $\omega^*_s(\mathcal{V}_n) = 1$ (witnessed by an oracularizable synchronous strategy), then $\omega^*_s(\mathcal{V}^{\mathrm{intro}}_n) = 1$;
- if $\omega^*(\mathcal{V}_n) \le 1/2$, then $\omega^*(\mathcal{V}^{\mathrm{intro}}_n) \le 1 - c$ for a universal constant $c > 0$.

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
