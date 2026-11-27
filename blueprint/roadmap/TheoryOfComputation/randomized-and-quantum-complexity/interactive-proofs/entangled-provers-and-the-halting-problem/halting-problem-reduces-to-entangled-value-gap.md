# The halting problem reduces to the entangled value gap problem

There is a computable map sending a Turing machine $M$ to a synchronous game $G_M$ (with conditionally linear questions) such that

- if $M$ halts on the empty input then $\omega^*(G_M) = 1$;
- if $M$ does not halt then $\omega^*(G_M) \le 1/2$.

## Proof sketch

By the recursion theorem build a normal form verifier $\mathcal{V}^M$ that on index $n$ runs $M$ for $n$ steps, accepts if $M$ has halted, and otherwise executes $\mathrm{Compress}(\mathcal{V}^M)$ at index $n$, i.e. simulates its own behaviour at index $2^n$. If $M$ halts at time $t$ then index $n \ge t$ is accepting and value $1$ propagates down by completeness of compression. If $M$ never halts, a value above $1/2$ at some index would force strategies of ever growing dimension at indices $2^n, 2^{2^n}, \dots$, contradicting finiteness of the dimension, so every index has value at most $1/2$; take $G_M = \mathcal{V}^M_{n_0}$.

## Depends on

- [Conditionally linear question distributions](conditionally-linear-question-distributions.md)
- [Synchronous two-prover games](synchronous-two-prover-games.md)
- [Uniformly generated families of two-prover one-round games](uniformly-generated-game-families.md)

## Proof depends on

- [Gap-preserving compression of normal form verifiers](gap-preserving-compression-of-normal-form-verifiers.md)
- [The halting problem is undecidable by multi-stack machines](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)
- [Parametrized s-m-n theorem](../../../computability/exists-computable-code.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
