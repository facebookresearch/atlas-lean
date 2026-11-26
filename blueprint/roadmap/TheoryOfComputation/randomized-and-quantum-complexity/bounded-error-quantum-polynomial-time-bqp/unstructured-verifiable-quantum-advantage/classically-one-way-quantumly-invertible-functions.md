# Functions that are classically one-way but quantumly invertible relative to a random oracle

Relative to a random oracle, there exist functions that are collision resistant (hence one-way) against classical polynomial-time adversaries yet can be inverted by quantum polynomial-time algorithms; analogous separations hold for digital signatures and, assuming a classically CPA-secure encryption scheme, for public-key encryption.

## Proof sketch

Define $f(x) = H'(x)$ restricted to the solution set of the codeword search problem, or more precisely compose the problem with a hash so that finding preimages requires producing valid codewords. Classical hardness of producing even one solution implies one-wayness, and the quantum sampler outputs uniformly random solutions, enough to find preimages and collisions.

## Depends on

- [Yamakawa-Zhandry: unconditional NP search separation relative to a random oracle](np-search-separation-relative-to-a-random-oracle.md)

## Proof depends on

- [Yamakawa-Zhandry: unconditional NP search separation relative to a random oracle](np-search-separation-relative-to-a-random-oracle.md)

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063.
