# Nonuniform one-way functions yield nonuniform pseudorandom generators

If $f$ is one-way against probabilistic polynomial-time adversaries with polynomially bounded advice, then there is a polynomial-time generator with one bit of stretch whose output is indistinguishable from uniform by every probabilistic polynomial-time distinguisher with polynomially bounded advice (equivalently, by every family of polynomial-size circuits).

## Proof sketch

Every reduction in Holenstein's construction maps an adversary with advice to an adversary with advice of the same length plus a polynomial, so the pseudoentropy pair of $f$ has its gap against advised predictors and the generator built from it is secure against advised distinguishers.

## Depends on

- [Security against adversaries with advice (nonuniform security)](../../../ComputerScience/cryptography/security-games/computational-indistinguishability-of-ensembles/security-against-adversaries-with-advice.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Pseudorandom generators against circuits](../derandomization/pseudorandom-generators-against-circuits.md)

## Proof depends on

- [One-way functions yield samplable pairs with an inverse-linear pseudoentropy gap](one-way-functions-yield-pseudoentropy-pairs.md)
- [Pseudorandom generators from samplable pseudoentropy pairs](pseudorandom-generators-from-pseudoentropy-pairs.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006.
- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A Pseudorandom Generator from Any One-Way Function", SIAM Journal on Computing 28(4), 1999.
