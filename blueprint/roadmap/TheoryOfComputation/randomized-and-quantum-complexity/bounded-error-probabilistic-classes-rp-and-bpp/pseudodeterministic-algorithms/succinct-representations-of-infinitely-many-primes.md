# Lu–Oliveira–Santhanam: infinitely many primes have representations of size O(|p|^ε)

For every $\varepsilon>0$ there are a fixed probabilistic polynomial-time algorithm $D$ and infinitely many primes $p$ such that each such $p$ has a string $w_p$ of length $O(|p|^{\varepsilon})$ with $D(w_p)=p$ with high probability. Equivalently, infinitely many primes have small probabilistic time-bounded Kolmogorov complexity relative to a fixed efficient decoder.

## Proof sketch

Use the pseudodeterministically computable PRG with seed length $m^{\varepsilon}$ for output length $m$. On a good length its outputs fool the AKS primality test, so a polynomial fraction of seeds map to primes by the prime number theorem. The representation of a prime is the seed (plus the advice bit), and $D$ runs the pseudodeterministic generator on it, outputting the same canonical prime with high probability.

## Proof depends on

- [Lu–Oliveira–Santhanam: a polynomial-stretch PRG computable pseudodeterministically with one advice bit](lu-oliveira-santhanam-pseudodeterministic-prg.md)
- [The n-bit primes form a dense polynomial-time decidable property](primes-are-dense-and-easy.md)

## Sources

- Zhenjian Lu, Igor C. Oliveira and Rahul Santhanam, "Pseudodeterministic Algorithms and the Structure of Probabilistic Time", STOC (2021), ECCC TR21-039.
