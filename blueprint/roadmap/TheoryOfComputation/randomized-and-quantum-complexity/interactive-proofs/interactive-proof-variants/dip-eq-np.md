# Deterministic interactive proofs capture exactly NP

Let $\mathsf{dIP}$ be the class of languages with an interactive proof in which the polynomial-time verifier is deterministic, completeness is $1$ and soundness error is $0$ (against arbitrary, even randomized, provers). Then $\mathsf{dIP}=\mathsf{NP}$.

## Proof sketch

A deterministic verifier's interaction is determined by the prover's messages, so the whole transcript is an NP certificate checkable by replaying the verifier; this is the deterministic case of the fact that interactive proofs with perfect soundness are in $\mathsf{NP}$. Conversely, an NP language has the one-message proof 'send the witness'.

## Depends on

- [The class IP](../../../complexity-classes/time-and-space-complexity-classes/ip.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Interactive proofs with perfect soundness are in NP](../../../pcp-and-inapproximability/pcp-verifiers-and-local-tests/perfect-soundness-interactive-proofs-in-np.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 8 (Theorem 8.3 of the January 2007 web draft; perfect soundness gives $\mathsf{NP}$ by its Exercise 8.1(e)).
