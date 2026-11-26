# Lu–Oliveira–Santhanam: a polynomial-stretch PRG computable pseudodeterministically with one advice bit

Unconditionally, there is a pseudorandom generator of polynomial stretch that is computable in pseudodeterministic polynomial time with one bit of advice and is secure infinitely often against polynomial-time computations. Pseudodeterministic computation means that on each seed the generator outputs one canonical string with high probability; infinitely-often security means that its outputs are indistinguishable from uniform by polynomial-time algorithms on infinitely many output lengths. It is the first such unconditional generator.

## Proof sketch

The construction builds on the techniques behind the Fortnow–Santhanam hierarchy theorem for probabilistic time with advice, where a single advice bit marks the input lengths on which a padded hard language behaves well. On such lengths the hardness is converted into pseudorandomness by a uniform hardness-randomness tradeoff, arranged so that every run recomputes the same hard truth table and hence the same generator output, which gives pseudodeterminism.

## Depends on

- [Pseudodeterministic algorithms for search problems (Gat–Goldwasser)](pseudodeterministic-algorithm-for-search-problem.md)
- [Pseudorandom generators against circuits](../../../pseudorandomness-and-one-way-functions/derandomization/pseudorandom-generators-against-circuits.md)

## Proof depends on

- [Impagliazzo-Wigderson: exponential circuit hardness in E derandomizes BPP](../../../pseudorandomness-and-one-way-functions/nisan-wigderson.md)

## Sources

- Zhenjian Lu, Igor C. Oliveira and Rahul Santhanam, "Pseudodeterministic Algorithms and the Structure of Probabilistic Time", STOC (2021), ECCC TR21-039.
