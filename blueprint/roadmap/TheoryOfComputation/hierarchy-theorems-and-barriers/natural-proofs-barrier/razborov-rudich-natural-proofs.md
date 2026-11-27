# Razborov-Rudich: the natural proofs barrier

Let $F = (F_n)_{n \in \mathbb{N}}$ be a keyed
family of Boolean functions, where $F_n(k, x)$ is a Boolean value for every key
$k \in \{0,1\}^{n^2}$ and every input $x \in \{0,1\}^n$. If $F$ is in P/poly (computed by circuits
of size polynomial in $n$) and is secure against truth-table distinguishers, then there is no
property $C = (C_n)_{n \in \mathbb{N}}$, with $C_n$ a set of Boolean functions on $n$ bits, that
is both natural and useful against P/poly.

The argument is short. By usefulness, at every large length $n$ no member $F_{n,k}$ of the family (each computed by a polynomial-size circuit with the key hard-wired) lies in $C_n$, while by largeness a uniformly random Boolean function lies in $C_n$ with probability at least $2^{-cn}$. The constructive decider for $C$ is therefore a truth-table distinguisher of size polynomial in $2^n$ with advantage at least $2^{-cn}$, contradicting security. Razborov and Rudich argue that the known lower-bound proofs for explicit Boolean functions in nonmonotone models, such as the bounds for constant-depth circuits, are natural; largeness reflects the fact that a random function is hard, as in [Shannon's counting bound](../../circuit-complexity/shannon-s-circuit-size-lower-bound/README.md).

The key length $n^2$ is a choice: with $n$-bit keys a distinguisher could hard-wire all $2^n$ members of the family, and in Razborov and Rudich's construction the key length is a polynomial in $n$ fixed by the hardness of the pseudorandom generator they start from, and their theorem assumes a pseudorandom generator rather than a pseudorandom function; this statement follows from their theorem, since evaluating the keyed function at fixed inputs gives a generator.

## Background

- [Shannon's circuit-size lower bound](../../circuit-complexity/shannon-s-circuit-size-lower-bound/README.md): almost all Boolean functions need large circuits, which is why lower-bound properties tend to be large.
- [Pseudorandom functions](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-functions/README.md): the
  cryptographic security experiment for keyed function families; security against truth-table
  distinguishers is the same requirement, with distinguishers of size polynomial in $2^n$ that read
  the whole truth table.

## Sources

- A. A. Razborov and S. Rudich, "Natural proofs", Journal of Computer and System Sciences 55 (1997), 24-35 (Proceedings of the Twenty-Sixth Annual ACM Symposium on Theory of Computing, STOC 1994, 18-27).
