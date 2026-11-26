# Publicly verifiable non-interactive proofs of quantumness relative to a random oracle

Relative to a random oracle there is a publicly verifiable proof of quantumness: a quantum prover outputs, without interaction, a string that anyone can check with polynomially many oracle queries, and no classical uniform polynomial-time prover produces an accepting string except with negligible probability; against non-uniform classical provers a two-message public-coin protocol suffices.

## Proof sketch

The proof is a solution of the codeword search problem for an instance derived from the random oracle (or, against non-uniform adversaries, from a fresh random salt sent by the verifier). Verification is the NP check, and soundness against classical provers is the query lower bound.

## Depends on

- [Search problems relative to a random oracle](search-problems-relative-to-a-random-oracle.md)

## Proof depends on

- [Yamakawa-Zhandry: unconditional NP search separation relative to a random oracle](np-search-separation-relative-to-a-random-oracle.md)

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063.
