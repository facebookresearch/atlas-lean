# Prediction from a leaked matrix hash yields inversion

Let $f$ be a function on $n$-bit inputs and $P$ a predictor of $\langle x, r\rangle$ from the hashed parity observation $(f(x), i, M, (Mx)_{1..i}, r)$. There is an inverter $A$, independent of the split point and of fiber sizes, that guesses the leaked hash prefix uniformly and runs Goldreich–Levin decoding with $P$ as oracle, such that if $P$'s correlation with the hidden bit exceeds $1 - H(B \mid X)$ by $\delta$ then $A$ inverts $f$ with probability at least a fixed polynomial in $\delta/n$.

## Proof sketch

Split the leaked prefix into a part of length about $\log|f^{-1}(f(x))| - O(\log(n/\delta))$, which is almost uniform on a fiber by the leftover hash lemma, and a short suffix that the inverter guesses at polynomial cost. With the almost-uniform part replaced by a guess, the predictor's advantage on the inner product survives, so Goldreich–Levin recovers $x$.

## Depends on

- [Hashed parity pair of a function](hashed-parity-pair.md)

## Proof depends on

- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)
- [Goldreich–Levin list decoding of the Hadamard code with oracle access](../hard-core-predicates-and-stretch/goldreich-levin-list-decoding.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006.
