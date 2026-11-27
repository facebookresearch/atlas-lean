# Interactive proofs with perfect soundness are in NP

Let $L$ have an interactive proof whose verifier runs in probabilistic polynomial time, accepts every $x \in L$ with some positive probability against some prover (positive completeness suffices), and accepts no $x \notin L$ with positive probability against any prover (perfect soundness). Then $L \in \mathrm{NP}$.

## Proof sketch

For $x \in L$ some transcript of polynomially many messages together with the verifier's coin sequence leads to acceptance; it is a polynomial-length certificate that can be checked by rerunning the verifier on those coins and messages. For $x \notin L$ no such accepting transcript exists, by perfect soundness.

## Depends on

- [The class IP](../../complexity-classes/time-and-space-complexity-classes/ip.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
