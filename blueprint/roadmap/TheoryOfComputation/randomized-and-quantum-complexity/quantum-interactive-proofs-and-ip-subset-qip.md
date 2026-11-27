# Quantum interactive proofs (QIP) and IP subset QIP

This node collects the definition of $\mathsf{QIP}$ and the inclusions involving classical interactive proofs.

## Expansion

A sound expansion has separate pages for:

1. **Definition.** $\mathsf{QIP}$ is the class of languages decided by a polynomial-time uniformly generated quantum
   verifier exchanging polynomially many quantum messages with an unbounded prover, with completeness at least $2/3$ and
   soundness at most $1/3$, using the interaction semantics of the prerequisite page.
2. **Embedding.** $\mathsf{IP} \subseteq \mathsf{QIP}$, by dephasing the message registers, so that a quantum prover is no more
   powerful than a classical one against a classical verifier.
3. **Consequence.** With $\mathsf{IP} = \mathsf{PSPACE}$, $\mathsf{PSPACE} \subseteq \mathsf{QIP}$. The equality
   $\mathsf{QIP} = \mathsf{PSPACE}$ is a separate theorem with its own source, not an ingredient proved here.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Quantum channels (CPTP maps).

## Depends on

- [BQP](../complexity-classes/time-and-space-complexity-classes/bqp.md)
- [Quantum interaction semantics](quantum-interaction-semantics.md)
- [The class IP](../complexity-classes/time-and-space-complexity-classes/ip.md)
- [Polynomial space for decision problems](../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [IP = PSPACE (Shamir)](ip-eq-pspace.md)

## Sources

- S. Aaronson, MIT 6.845 Quantum Complexity Theory, Lecture 17 (scribe notes), item 3 (Theorem 1, LFKN and Shamir, IP = PSPACE) and §2 (definition of QIP; "Certainly IP ⊆ QIP ... Thus PSPACE ⊆ QIP"). <https://old.ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-845-quantum-complexity-theory-fall-2010/lecture-notes/MIT6_845F10_lec17.pdf>
- J. Watrous, "Quantum computational complexity", arXiv:0804.3401, Section VI.1 (the classes QIP$(m, a, b)$ and QIP $= \bigcup_m$ QIP$(m, 2/3, 1/3)$) and Section VI.2 (classical interactive proofs are simulated by quantum ones, so PSPACE ⊆ QIP). <https://arxiv.org/abs/0804.3401>
- R. Jain, Z. Ji, S. Upadhyay and J. Watrous, "QIP = PSPACE", arXiv:0907.4737 (J. ACM 58 (2011)), abstract and Section 1. <https://arxiv.org/abs/0907.4737>
