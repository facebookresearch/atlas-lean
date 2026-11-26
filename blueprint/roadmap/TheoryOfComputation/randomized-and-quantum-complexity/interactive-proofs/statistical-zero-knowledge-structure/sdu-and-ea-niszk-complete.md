# Goldreich–Sahai–Vadhan: Statistical Difference from Uniform and Entropy Approximation are NISZK-complete

**Statistical Difference from Uniform** is the promise problem $\mathrm{SDU}$ on circuits $X$ with $n$ output bits: YES if $\Delta(X,U_n)<1/n$ and NO if $\Delta(X,U_n)>1-1/n$, where $\Delta$ is statistical distance and $U_n$ is uniform on $\{0,1\}^n$. Both $\mathrm{SDU}$ and Entropy Approximation $\mathrm{EA}$ are complete for $\mathsf{NISZK}$ under Karp reductions; they are the one-sided restrictions, with the second distribution fixed to uniform, of the $\mathsf{SZK}$-complete problems statistical difference and entropy difference.

## Proof sketch

For membership, the common random string is a candidate output $y$ and the prover sends a uniformly random preimage of $y$ under $X$; when $X$ is close to uniform this is simulable by sampling an input and outputting it with its image, and when $X$ is far from uniform a random $y$ has no preimage with high probability (after polarizing the gap). For hardness, the simulator of an arbitrary $\mathsf{NISZK}$ proof, restricted to its common-random-string component, is close to uniform on YES instances and far from uniform on NO instances, by soundness.

## Depends on

- [Non-interactive statistical zero knowledge NISZK in the common random string model](niszk-common-random-string.md)
- [The Entropy Difference problem ED](entropy-difference-problem.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Non-interactive statistical zero knowledge NISZK in the common random string model](niszk-common-random-string.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- Oded Goldreich, Amit Sahai and Salil Vadhan, "Can Statistical Zero Knowledge be made Non-Interactive? or On the Relationship of SZK and NISZK", CRYPTO (1999), ECCC TR99-013.
