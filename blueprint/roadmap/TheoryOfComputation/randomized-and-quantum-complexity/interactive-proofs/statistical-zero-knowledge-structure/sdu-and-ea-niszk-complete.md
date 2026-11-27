# Goldreich–Sahai–Vadhan: Statistical Difference from Uniform and Entropy Approximation are NISZK-complete

**Statistical Difference from Uniform** is the promise problem $\mathrm{SDU}$ on circuits $X$ with $n$ output bits: YES if $\Delta(X,U_n)<1/n$ and NO if $\Delta(X,U_n)>1-1/n$, where $\Delta$ is statistical distance and $U_n$ is uniform on $\{0,1\}^n$. Both $\mathrm{SDU}$ and Entropy Approximation $\mathrm{EA}$ are complete for $\mathsf{NISZK}$ under Karp reductions; they are the one-sided restrictions, with the second distribution fixed to uniform, of the $\mathsf{SZK}$-complete problems statistical difference and entropy difference.

## Proof sketch

For membership, $\mathrm{SDU}$ Karp-reduces to $\mathrm{EA}$ (the map $X\mapsto(X,n-3)$), and $\mathrm{EA}$ has an $\mathsf{NISZK}$ proof; a preimage of the reference string is not by itself a soundness certificate, since a sampler arbitrarily far from uniform can still have full support. For hardness, take an $\mathsf{NISZK}$ proof, repeated in parallel so that its completeness and soundness errors are at most $2^{-m}$ with $2^{1-m/2}+2^{-r}<1/r$ for its reference string length $r$, and a simulator $S$; map $x$ to the circuit $M_x$ that, on its input, runs $S(x)$ to get a transcript $(\sigma,p)$, runs the verifier on $(x,\sigma,p)$ with coins also taken from its input, and outputs $\sigma$ if the verifier accepts and a fixed string $0^{r}$ otherwise. On YES instances $M_x$ is within $1/r$ of uniform by simulation and completeness. On NO instances let $a(\sigma)=\max_p\Pr[V(x,\sigma,p)\text{ accepts}]$ over the verifier's coins; the prover strategy that sends a maximizing $p$ shows $\mathbb{E}_\sigma[a(\sigma)]\le 2^{-m}$, so by Markov's inequality the set $B$ of reference strings with $a(\sigma)\ge 2^{-m/2}$ has density at most $2^{-m/2}$. Since $\Pr[M_x=\sigma]\le\Pr[S(x)\text{ outputs }\sigma]\cdot a(\sigma)$, the circuit $M_x$ puts total mass at most $2^{-m/2}$ outside $B\cup\{0^r\}$, while the uniform distribution puts mass at least $1-2^{-m/2}-2^{-r}$ there, so $M_x$ is at distance more than $1-1/r$ from uniform.

## Depends on

- [Non-interactive statistical zero knowledge NISZK in the common random string model](niszk-common-random-string.md)
- [The Entropy Difference problem ED](entropy-difference-problem.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- Oded Goldreich, Amit Sahai and Salil Vadhan, "Can Statistical Zero Knowledge be made Non-Interactive? or On the Relationship of SZK and NISZK", CRYPTO (1999), ECCC TR99-013 (Lemmas 4.1–4.2).
