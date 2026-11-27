# Gap-preserving compression of normal form verifiers

There is a computable map $\mathcal{V} \mapsto \mathcal{V}' = \mathrm{Compress}(\mathcal{V})$ on normal form verifiers and a polynomial $p$ such that for every $\mathcal{V}$ and all $n$ larger than a threshold computable from $\mathcal{V}$:

1. the sampler and decider of $\mathcal{V}'_n$ run in time $p(n, |\mathcal{V}|)$;
2. if $\omega^*_s(\mathcal{V}_{2^n}) = 1$ then $\omega^*_s(\mathcal{V}'_n) = 1$;
3. if $\omega^*(\mathcal{V}_{2^n}) \le 1/2$ then $\omega^*(\mathcal{V}'_n) \le 1/2$;
4. the minimal local dimension $\mathcal{E}(\mathcal{V}'_n, 1/2)$ of a strategy for $\mathcal{V}'_n$ with value at least $1/2$ satisfies $\mathcal{E}(\mathcal{V}'_n, 1/2) \ge \max\{\mathcal{E}(\mathcal{V}_{2^n}, 1/2),\, 2^{2^{\Omega(n)}}\}$.

## Proof sketch

Apply introspection to reduce question length exponentially, then answer reduction to reduce decision time exponentially; both preserve completeness and degrade soundness to $1 - c$. Anchored parallel repetition with a polynomial number of copies restores soundness $1/2$ while keeping the verifier efficient and preserving completeness. The resulting verifier at index $n$ simulates the original at index $2^n$ in time polynomial in $n$.

## Depends on

- [Conditionally linear question distributions](conditionally-linear-question-distributions.md)
- [Synchronous two-prover games](synchronous-two-prover-games.md)
- [Uniformly generated families of two-prover one-round games](uniformly-generated-game-families.md)

## Proof depends on

- [Question reduction by introspection](question-reduction-by-introspection.md)
- [Answer reduction through oracularization and probabilistically checkable proofs](answer-reduction-by-probabilistically-checkable-proofs.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
- Joseph Fitzsimons, Zhengfeng Ji, Thomas Vidick, Henry Yuen, "Quantum proof systems for iterated exponential time, and beyond", STOC (2019); arXiv:1805.12166.
