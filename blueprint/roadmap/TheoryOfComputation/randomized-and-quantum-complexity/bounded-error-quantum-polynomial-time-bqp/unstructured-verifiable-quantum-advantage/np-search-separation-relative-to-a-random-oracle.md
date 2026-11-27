# Yamakawa-Zhandry: unconditional NP search separation relative to a random oracle

Relative to a random oracle $H$, with probability $1$ over $H$, there is an NP search problem that is solvable by a quantum polynomial-time algorithm but by no classical probabilistic polynomial-time algorithm: $\mathrm{FNP}^H \cap \mathrm{FBQP}^H \not\subseteq \mathrm{FBPP}^H$. The problem has no algebraic or periodic structure beyond the random oracle itself.

## Proof sketch

Instantiate the codeword search problem with folded Reed-Solomon codes. The quantum algorithm succeeds by dual decoding, classical algorithms fail by list recoverability, and solutions are checkable with $n$ oracle queries. A Borel-Cantelli argument over input lengths upgrades the per-length separation to probability one over $H$.

## Depends on

- [Search problems relative to a random oracle](search-problems-relative-to-a-random-oracle.md)

## Proof depends on

- [Folded Reed-Solomon codes satisfy the dual-decodability and list-recovery conditions](folded-reed-solomon-codes-meet-both-conditions.md)

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063.
