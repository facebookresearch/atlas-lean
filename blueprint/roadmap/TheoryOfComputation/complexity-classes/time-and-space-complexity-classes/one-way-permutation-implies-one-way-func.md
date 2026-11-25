# One-way permutations are one-way functions

Let $\pi$ be a one-way permutation family, so
that each $\pi_n$ maps $n$-bit strings to $n$-bit strings. Then the family that sends an $n$-bit
string $x$ to the bitstring $\pi_n(x)$ is a one-way function family.

Length preservation gives the polynomial output bound, the evaluator of $\pi$ serves unchanged,
and the inversion success probabilities coincide because an $n$-bit string is determined by the
list of its bits.

## Sources

- O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University Press, 2001, Section 2.2.
