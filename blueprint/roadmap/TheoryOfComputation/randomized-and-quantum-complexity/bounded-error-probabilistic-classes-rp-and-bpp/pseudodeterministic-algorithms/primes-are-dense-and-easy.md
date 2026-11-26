# The n-bit primes form a dense polynomial-time decidable property

Let $Q_n$ be the set of $n$-bit binary strings (leading bit $1$) encoding a prime. There is a constant $\rho$ such that $|Q_n|\ge n^{-\rho}2^n$ for all $n\ge 2$, and $Q=\bigcup_n Q_n$ is decidable in deterministic polynomial time. Hence $Q$ is dense and easy, and any pseudodeterministic construction for dense easy properties yields one for primes.

## Proof sketch

By the prime number theorem the number of primes in $[2^{n-1},2^n)$ is $(1+o(1))2^{n-1}/(n\ln 2)$, which is at least $2^n/(2n)$ for large $n$, and a finite check handles small $n$. Membership is decided by the AKS primality test in polynomial time.

## Depends on

- [Pseudodeterministic constructions for dense properties, everywhere and infinitely often](pseudodeterministic-construction-of-dense-property.md)

## Proof depends on

- [Prime number theorem](../../../../NumberTheory/distribution-of-primes/prime-number-theorem/prime-number-theorem/prime-number-theorem.md)
- [PRIMES is in P](../../../polynomial-time-problems/aks-primality-test/primes-in-p.md)

## Sources

- Lijie Chen, Zhenjian Lu, Igor C. Oliveira, Hanlin Ren and Rahul Santhanam, "Polynomial-Time Pseudodeterministic Construction of Primes", FOCS (2023), arXiv:2305.15140.
