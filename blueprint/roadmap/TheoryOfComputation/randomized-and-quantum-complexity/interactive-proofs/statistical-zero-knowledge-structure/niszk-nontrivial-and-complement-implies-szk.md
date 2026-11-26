# Goldreich–Sahai–Vadhan: SZK ≠ BPP implies NISZK ≠ BPP, and NISZK closed under complement implies NISZK = SZK

1. If $\mathsf{SZK}$ contains a promise problem outside $\mathsf{BPP}$, then so does $\mathsf{NISZK}$.
2. If $\mathsf{NISZK}$ is closed under complement, then $\mathsf{NISZK}=\mathsf{SZK}$: every statistical zero-knowledge proof can then be made non-interactive.
3. A weak form of $\mathsf{NISZK}$, in which for every inverse polynomial $1/p(n)$ there is a simulator with deviation $1/p(n)$, equals $\mathsf{NISZK}$.

## Proof sketch

The proofs pass through the complete problems: there are Karp reductions from $\mathrm{ED}$ to combinations of instances of $\mathrm{EA}$ and its complement (compare each entropy to a guessed threshold), so if $\mathrm{EA}$ were easy then $\mathrm{ED}$ would be easy, which gives item 1, and if $\overline{\mathrm{EA}}$ were in $\mathsf{NISZK}$ then $\mathrm{ED}$ would be too, which gives item 2. Item 3 follows by showing the weak-simulation version of $\mathrm{SDU}$ reduces to $\mathrm{SDU}$ itself.

## Depends on

- [Non-interactive statistical zero knowledge NISZK in the common random string model](niszk-common-random-string.md)
- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)

## Proof depends on

- [Goldreich–Sahai–Vadhan: Statistical Difference from Uniform and Entropy Approximation are NISZK-complete](sdu-and-ea-niszk-complete.md)
- [Goldreich–Vadhan: every HVSZK problem Karp-reduces to Entropy Difference](every-hvszk-problem-reduces-to-ed.md)
- [Goldreich–Vadhan: Entropy Difference has a public-coin honest-verifier statistical zero-knowledge proof](entropy-difference-has-public-coin-hvszk-proof.md)

## Sources

- Oded Goldreich, Amit Sahai and Salil Vadhan, "Can Statistical Zero Knowledge be made Non-Interactive? or On the Relationship of SZK and NISZK", CRYPTO (1999), ECCC TR99-013.
