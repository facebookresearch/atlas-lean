# Goldreich–Vadhan: Entropy Difference has a public-coin honest-verifier statistical zero-knowledge proof

$\mathrm{ED}$ has a public-coin honest-verifier statistical zero-knowledge proof system with a polynomial-time verifier. Consequently $\mathrm{ED}$ is complete for $\mathsf{HVSZK}$ under Karp reductions, and every problem in $\mathsf{HVSZK}$ has a public-coin $\mathsf{HVSZK}$ proof.

## Proof sketch

Using flattening (taking many independent copies makes each distribution close to flat, so Shannon entropy governs min-entropy and max-entropy up to small loss) and hashing, an instance $(X,Y)$ of ED is converted into a pair of circuits whose statistical distance is large when $H(X)\ge H(Y)+1$ and small otherwise; the polarized statistical-difference instance then has a public-coin protocol in which the verifier sends random coins and the prover answers which of two samplers produced a hashed value. The simulator reproduces the transcript by sampling the circuits itself, giving statistical zero knowledge for the honest verifier.

## Depends on

- [The Entropy Difference problem ED](entropy-difference-problem.md)
- [Public-coin interactive proofs](../../goldwasser-sipser-theorem/pub-ip.md)

## Proof depends on

- [Goldreich–Vadhan: every HVSZK problem Karp-reduces to Entropy Difference](every-hvszk-problem-reduces-to-ed.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- Oded Goldreich and Salil Vadhan, "Comparing Entropies in Statistical Zero Knowledge with Applications to the Structure of SZK", CCC (1999), ECCC TR98-063.
