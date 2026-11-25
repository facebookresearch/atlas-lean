# BQP is contained in QIP

Every language in BQP has a quantum interactive proof with zero messages and the same completeness and soundness: the
verifier runs the BQP circuit on its private register and accepts on its output, ignoring the prover. Hence $\mathrm{BQP} \subseteq \mathrm{QIP}$. If the definition of QIP requires at least one message, the same holds with one prover message that the verifier discards.

## Proof

With zero messages there are no prover channels, so the acceptance probability of every prover equals the probability that the
verifier's own circuit accepts, which is at least $2/3$ on inputs in the language and at most $1/3$ otherwise.

## Depends on

- [Quantum interactive proofs (QIP) and IP subset QIP](quantum-interactive-proofs-and-ip-subset-qip.md)
- [BQP](../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Proof depends on

- [Quantum interaction semantics](quantum-interaction-semantics.md)

## Sources

- J. Watrous, *Quantum computational complexity*, arXiv:0804.3401, Section VI.1 (definition of quantum interactive proofs and the classes QIP(m, a, b)). <https://arxiv.org/abs/0804.3401>
