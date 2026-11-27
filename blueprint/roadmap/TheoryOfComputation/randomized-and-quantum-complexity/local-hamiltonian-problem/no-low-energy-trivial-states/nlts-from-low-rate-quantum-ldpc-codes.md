# Golowich-Kaufman: NLTS Hamiltonians from low-rate quantum LDPC codes

There are families of quantum LDPC codes with vanishing rate (dimension $k = o(n)$) whose code Hamiltonians still have the NLTS property, provided the codes have linear distance and an appropriate small-set expansion of the checks; the same codes yield strongly explicit sum-of-squares lower bounds for constraint satisfaction problems.

## Proof sketch

Replace the uncertainty argument based on many logical qubits by a counting argument over approximate codewords: small-set expansion forces the low-energy measurement distributions to be close to uniform mixtures over many clusters, which shallow circuits cannot produce because of the spread lemma. The degree-two structure of the code checks transfers to sum-of-squares certificates.

## Depends on

- [CSS code Hamiltonians of quantum LDPC codes](css-code-hamiltonians.md)
- [The NLTS property and the Freedman-Hastings conjecture](no-low-energy-trivial-states-property.md)

## Proof depends on

- [NLTS theorem (Anshu-Breuckmann-Nirkhe)](nlts-hamiltonians-from-good-quantum-codes.md)
- [Clustering of low-syndrome strings for codes with small-set boundary expansion](clustering-of-low-syndrome-strings.md)

## Sources

- Louis Golowich, Tali Kaufman, "NLTS Hamiltonians and strongly-explicit SoS lower bounds from low-rate quantum LDPC codes", ITCS (2024); ECCC TR23-178.
