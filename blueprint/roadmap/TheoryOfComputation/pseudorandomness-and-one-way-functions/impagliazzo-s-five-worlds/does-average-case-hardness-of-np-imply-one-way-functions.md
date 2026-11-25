# Does average-case hardness of NP imply one-way functions?

If some problem in NP is hard on average, under a fixed notion of distributional hardness, must one-way functions exist? Equivalently, can Pessiland, a world in which NP is hard on average but one-way functions do not exist, be ruled out? This is not the statement that P ≠ NP implies one-way functions: worst-case and average-case hardness differ.

## Depends on

- [Pessiland](pessiland.md)
- [One-way functions exist](owfexists.md)

## What would settle it

Fix one definition of average-case hardness of distributional NP problems and one definition of one-way functions (including uniform or nonuniform adversaries), and prove that the hardness assumption implies the existence of one-way functions, or that it does not. Relativized separations do not settle it: the cited source recalls an oracle relative to which some language in NP ∩ coNP is hard on average while one-way functions do not exist (Wee 2006, after Impagliazzo and Rudich).

## Status

No cited source poses this question in the form above; this page does not certify its present status. The status evidence is incomplete; check later literature before relying on it.

Chen, Morimae and Yamakawa describe Pessiland, after Impagliazzo (1995), as a world where NP is hard on average but one-way functions do not exist, note that almost all classical cryptographic primitives imply one-way functions, and study a quantum analogue.

This page records a research question and asserts no theorem or present-status certification.

## Sources

- B. Chen, T. Morimae and T. Yamakawa, "Quantum Pessiland", preprint (2026), abstract and introduction. <https://arxiv.org/abs/2608.29493>
