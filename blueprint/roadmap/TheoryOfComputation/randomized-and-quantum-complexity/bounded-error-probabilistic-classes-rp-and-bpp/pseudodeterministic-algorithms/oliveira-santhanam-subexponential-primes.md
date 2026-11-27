# Oliveira–Santhanam: infinitely-often pseudodeterministic construction of primes in subexponential time

Unconditionally, for every constant $\varepsilon > 0$ there exist an infinite sequence $p_1<p_2<\cdots$ of primes and a randomized zero-error algorithm $A$ running in expected time $O(2^{m^{\varepsilon}})$ on inputs of length $m$ such that, for each $n$, on input $1^{|p_n|}$ the algorithm outputs $p_n$ with probability $1$ (Oliveira–Santhanam, Theorem 1; this proof establishes existence of $A$ non-constructively without exhibiting which branch of the dichotomy holds). Separately (Theorem 3), there is an **explicit** bounded-error pseudodeterministic algorithm running in subexponential time that outputs a canonical prime $q_n$ with probability $1 - o(1)$ on infinitely many lengths satisfying $|q_{n+1}| < |q_n|^k$ (for a constant $k$), which does not strictly subsume Theorem 1 because it has bounded error rather than zero error.

## Proof sketch

Apply the hitting-set dichotomy to the dense easy property of primes. In the first case, scanning a pseudodeterministically produced hitting set with the AKS test and outputting the first prime gives a canonical prime on all large lengths. In the second case, deterministically enumerating a subexponential-time hitting set and outputting its first prime works on infinitely many lengths. Because the proof does not determine which case holds, Theorem 1 yields a non-constructive zero-error algorithm; a separate bounded-error win-win yields the explicit algorithm of Theorem 3.

## Depends on

- [Pseudodeterministic constructions for dense properties, everywhere and infinitely often](pseudodeterministic-construction-of-dense-property.md)

## Proof depends on

- [Oliveira–Santhanam: pseudodeterministic polynomial-time hitting sets or deterministic subexponential ones](oliveira-santhanam-hitting-set-dichotomy.md)
- [The n-bit primes form a dense polynomial-time decidable property](primes-are-dense-and-easy.md)

## Sources

- Igor C. Oliveira and Rahul Santhanam, "Pseudodeterministic Constructions in Subexponential Time", STOC (2017), ECCC TR16-196.
