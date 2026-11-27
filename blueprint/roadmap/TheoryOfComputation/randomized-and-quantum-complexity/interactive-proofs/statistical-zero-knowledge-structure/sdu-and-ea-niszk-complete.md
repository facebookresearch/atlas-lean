# Goldreich–Sahai–Vadhan: Statistical Difference from Uniform and Entropy Approximation are NISZK-complete

**Statistical Difference from Uniform** is the promise problem $\mathrm{SDU}$ on circuits $X$ with $n$ output bits: YES if $\Delta(X,U_n)<1/n$ and NO if $\Delta(X,U_n)>1-1/n$, where $\Delta$ is statistical distance and $U_n$ is uniform on $\{0,1\}^n$. Both $\mathrm{SDU}$ and Entropy Approximation $\mathrm{EA}$ are complete for $\mathsf{NISZK}$ under Karp reductions; they are the one-sided restrictions, with the second distribution fixed to uniform, of the $\mathsf{SZK}$-complete problems statistical difference and entropy difference.

## Proof sketch

For membership, $\mathrm{SDU}$ Karp-reduces to $\mathrm{EA}$ (the map $X\mapsto(X,n-3)$), and $\mathrm{EA}$ has an $\mathsf{NISZK}$ proof; a preimage of the reference string is not by itself a soundness certificate, since a sampler arbitrarily far from uniform can still have full support. For hardness, given an $\mathsf{NISZK}$ proof with completeness and soundness errors at most $2^{-n}$ and a simulator $S$, map $x$ to the circuit $M_x$ that runs $S(x)$ on its input to get a transcript $(\sigma,p)$ and outputs $\sigma$ if the verifier accepts $(x,\sigma,p)$ and a fixed string $0^{r}$ otherwise. On YES instances $M_x$ is within $1/r$ of uniform by simulation and completeness; on NO instances soundness leaves at most a $2^{-n}$ fraction of reference strings with an accepting transcript, so $M_x$ is at distance more than $1-1/r$ from uniform.

## Depends on

- [Non-interactive statistical zero knowledge NISZK in the common random string model](niszk-common-random-string.md)
- [The Entropy Difference problem ED](entropy-difference-problem.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- Oded Goldreich, Amit Sahai and Salil Vadhan, "Can Statistical Zero Knowledge be made Non-Interactive? or On the Relationship of SZK and NISZK", CRYPTO (1999), ECCC TR99-013 (Lemmas 4.1–4.2).
