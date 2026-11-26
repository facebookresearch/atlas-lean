# Chen–Lu–Oliveira–Ren–Santhanam: polynomial-time pseudodeterministic construction of n-bit primes for infinitely many n

There is an unconditional randomized polynomial-time algorithm $B$ such that, for infinitely many $n$, $B(1^n)$ outputs a canonical $n$-bit prime $p_n$ with high probability (and on every length it outputs either $p_n$ or $\bot$ except with probability $2^{-n}$). This resolves, in the infinitely-often regime, the question of Gat and Goldwasser whether primes can be constructed pseudodeterministically in polynomial time, improving the subexponential construction of Oliveira and Santhanam.

## Proof sketch

Apply the general theorem for dense easy properties to the primes, which are dense by the prime number theorem and easy by the AKS test.

## Depends on

- [Pseudodeterministic constructions for dense properties, everywhere and infinitely often](pseudodeterministic-construction-of-dense-property.md)

## Proof depends on

- [Chen–Lu–Oliveira–Ren–Santhanam: infinitely-often polynomial-time pseudodeterministic constructions for every dense easy property](polynomial-time-pseudodeterministic-construction-dense-properties.md)
- [The n-bit primes form a dense polynomial-time decidable property](primes-are-dense-and-easy.md)

## Sources

- Lijie Chen, Zhenjian Lu, Igor C. Oliveira, Hanlin Ren and Rahul Santhanam, "Polynomial-Time Pseudodeterministic Construction of Primes", FOCS (2023), arXiv:2305.15140.
