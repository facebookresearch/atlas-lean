# One-way functions imply adaptively secure pseudorandom functions

If a one-way function exists, then there is a length-preserving keyed function family $F_k : \{0,1\}^n \to \{0,1\}^n$ ($|k| = n$), evaluable in deterministic polynomial time, such that every probabilistic polynomial-time oracle adversary making adaptive queries distinguishes $F_k$ for a uniform key from a uniformly random function with negligible advantage.

## Proof sketch

One-way functions give pseudorandom generators (Håstad–Impagliazzo–Levin–Luby), stretch amplification gives a length-doubling generator, and the Goldreich–Goldwasser–Micali tree construction turns a length-doubling generator into a pseudorandom function.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Asymptotic PRF security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-functions/prfsecure.md)

## Proof depends on

- [Pseudorandom generators exist if and only if one-way functions exist](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)
- [Stretch amplification of a one-bit pseudorandom generator](prg-stretch-amplification.md)
- [The GGM construction: pseudorandom generators give pseudorandom functions](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-functions/the-ggm-construction-pseudorandom-generators.md)

## Sources

- O. Goldreich, S. Goldwasser and S. Micali, "How to Construct Random Functions", Journal of the ACM 33(4), 1986.
- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A Pseudorandom Generator from Any One-Way Function", SIAM Journal on Computing 28(4), 1999.
- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006.
