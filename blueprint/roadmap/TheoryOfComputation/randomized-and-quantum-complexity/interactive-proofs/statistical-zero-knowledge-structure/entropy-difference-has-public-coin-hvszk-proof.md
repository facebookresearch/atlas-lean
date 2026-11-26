# Goldreich–Vadhan: Entropy Difference has a public-coin honest-verifier statistical zero-knowledge proof

$\mathrm{ED}$ has a public-coin honest-verifier statistical zero-knowledge proof system with a polynomial-time verifier. Consequently $\mathrm{ED}$ is complete for $\mathsf{HVSZK}$ under Karp reductions, and every problem in $\mathsf{HVSZK}$ has a public-coin $\mathsf{HVSZK}$ proof.

## Proof sketch

Using flattening (taking many independent copies makes each distribution close to flat, so Shannon entropy governs min-entropy and max-entropy up to small loss) and hashing, Goldreich and Vadhan give a direct public-coin protocol for $\mathrm{ED}$: every verifier message is a uniformly random hash function or target value, and the prover answers with preimages under the flattened samplers, so that, as in the Goldwasser–Sipser set lower-bound protocol, the verifier compares the sizes of typical preimage sets, which flatness ties to the entropies. The simulator reproduces the transcript by sampling the circuits itself, giving statistical zero knowledge for the honest verifier.

## Depends on

- [The Entropy Difference problem ED](entropy-difference-problem.md)
- [Public-coin interactive proofs](../../goldwasser-sipser-theorem/pub-ip.md)
- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)

## Proof depends on

- [Goldreich–Vadhan: every HVSZK problem Karp-reduces to Entropy Difference](every-hvszk-problem-reduces-to-ed.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- Oded Goldreich and Salil Vadhan, "Comparing Entropies in Statistical Zero Knowledge with Applications to the Structure of SZK", CCC (1999), ECCC TR98-063.
