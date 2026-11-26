# Chen–Lu–Oliveira–Ren–Santhanam: infinitely-often polynomial-time pseudodeterministic constructions for every dense easy property

Let $Q\subseteq\{0,1\}^*$ satisfy: there is $\rho\ge 1$ with $|Q_n|\ge n^{-\rho}2^n$ for every $n\ge 1$, and $Q$ is decided by a deterministic polynomial-time algorithm $A_Q$. Then there are a probabilistic polynomial-time algorithm $B$ and strings $x_n\in Q_n$ such that

1. for every $n\ge 1$, $\Pr[B(1^n)\notin\{x_n,\bot\}]\le 2^{-n}$, and
2. for infinitely many $n$, $\Pr[B(1^n)=x_n]\ge 1-2^{-n}$.

The construction is non-black-box: the canonical outputs $x_n$ depend on the code of $A_Q$.

## Proof sketch

Run the bootstrapping recursion from infinitely many, sufficiently spread out initial lengths $n_0^{(1)}<n_0^{(2)}<\cdots$; each chain of $O(\log n_0)$ lengths contains a length where the algorithm succeeds, which gives the second condition. On every length the algorithm checks its candidate with $A_Q$ and outputs $\bot$ unless the reconstruction is consistent, and a general argument from Oliveira–Santhanam upgrades this to the first condition.

## Depends on

- [Pseudodeterministic constructions for dense properties, everywhere and infinitely often](pseudodeterministic-construction-of-dense-property.md)

## Proof depends on

- [Bootstrapping win-win: recursive hitting sets over lengths n_{i+1} = n_i^β](bootstrapping-recursive-hitting-sets.md)

## Sources

- Lijie Chen, Zhenjian Lu, Igor C. Oliveira, Hanlin Ren and Rahul Santhanam, "Polynomial-Time Pseudodeterministic Construction of Primes", FOCS (2023), arXiv:2305.15140.
