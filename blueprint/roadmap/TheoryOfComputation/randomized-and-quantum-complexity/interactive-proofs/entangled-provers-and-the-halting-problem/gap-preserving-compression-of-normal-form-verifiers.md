# Gap-preserving compression of normal form verifiers

There is a computable map $(\mathcal{V}, \lambda) \mapsto \mathcal{V}' = \mathrm{Compress}(\mathcal{V}, \lambda)$ taking a normal form verifier $\mathcal{V} = (S, D)$ and a complexity parameter $\lambda \in \mathbb{N}$ (where $\mathcal{V}$ is **$\lambda$-bounded** if $|\mathcal{V}| \le \lambda$ and its sampler and decider satisfy $\mathrm{TIME}_S(n), \mathrm{TIME}_D(n) \le n^\lambda$ for all $n \ge 2$, Ji–Natarajan–Vidick–Wright–Yuen Definition 5.32) to a normal form verifier $\mathcal{V}'$, and a universal constant $C_0$, such that (Theorem 12.1, arXiv:2001.04383v4):

1. the sampler and decider of $\mathcal{V}'_n$ run in time $\mathrm{poly}(n, \lambda)$;
2. if $\mathcal{V}$ is a $\lambda$-bounded $9$-level normal form verifier and $n \ge C_0$ (with $N = 2^n$), then:
   - *(Completeness)* if $\mathcal{V}_N$ has a value-$1$ projective, consistent, commuting (PCC) strategy, then $\mathcal{V}'_n$ has a value-$1$ PCC strategy;
   - *(Soundness)* if $\omega^*(\mathcal{V}_N) \le 1/2$, then $\omega^*(\mathcal{V}'_n) \le 1/2$;
   - *(Entanglement)* the minimal local dimension $\mathcal{E}(\mathcal{V}'_n, 1/2)$ of a strategy for $\mathcal{V}'_n$ with value at least $1/2$ satisfies $\mathcal{E}(\mathcal{V}'_n, 1/2) \ge \max\{\tfrac{1}{2}\mathcal{E}(\mathcal{V}_N, 1/2),\, 2^{N^\lambda - 1}\}$.

## Proof sketch

Apply introspection to reduce question length exponentially, then answer reduction to reduce decision time exponentially; both preserve value-$1$ PCC strategies and degrade soundness to $1 - 1/\mathrm{poly}(\lambda n)$. Anchored parallel repetition with $k(n) = (\lambda n)^{\tau}$ copies (a polynomial number of repetitions, Theorem 11.4) restores soundness $1/2$ while keeping the verifier efficient and preserving value-$1$ PCC completeness. The resulting verifier at index $n$ simulates the $\lambda$-bounded $9$-level verifier at index $N = 2^n$ in time $\mathrm{poly}(n, \lambda)$.

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
