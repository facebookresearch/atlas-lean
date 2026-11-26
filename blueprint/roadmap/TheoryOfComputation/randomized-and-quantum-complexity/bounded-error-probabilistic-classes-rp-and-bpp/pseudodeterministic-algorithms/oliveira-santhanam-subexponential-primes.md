# Oliveira–Santhanam: infinitely-often pseudodeterministic construction of primes in subexponential time

Unconditionally, there is an infinite sequence $p_1<p_2<\cdots$ of primes and a randomized zero-error algorithm $A$ running in expected subexponential time such that, for each $n$, on input $1^{|p_n|}$ the algorithm outputs $p_n$. That is, primes have an infinitely-often pseudodeterministic construction in subexponential time; the construction is explicit although the proof is non-constructive about which case of the underlying dichotomy holds.

## Proof sketch

Apply the hitting-set dichotomy to the dense easy property of primes. In the first case, scanning a pseudodeterministically produced hitting set with the AKS test and outputting the first prime gives a canonical prime on all large lengths. In the second case, deterministically enumerating a subexponential-time hitting set and outputting its first prime works on infinitely many lengths. Further properties of the tradeoff are used to merge the two cases into one explicit algorithm.

## Depends on

- [Pseudodeterministic constructions for dense properties, everywhere and infinitely often](pseudodeterministic-construction-of-dense-property.md)

## Proof depends on

- [Oliveira–Santhanam: pseudodeterministic polynomial-time hitting sets or deterministic subexponential ones](oliveira-santhanam-hitting-set-dichotomy.md)
- [The n-bit primes form a dense polynomial-time decidable property](primes-are-dense-and-easy.md)

## Sources

- Igor C. Oliveira and Rahul Santhanam, "Pseudodeterministic Constructions in Subexponential Time", STOC (2017), ECCC TR16-196.
