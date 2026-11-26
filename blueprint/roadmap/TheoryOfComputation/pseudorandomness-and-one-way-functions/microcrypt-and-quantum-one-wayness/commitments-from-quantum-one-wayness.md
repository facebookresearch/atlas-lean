# Quantum commitments and secure computation from one-way state generators

If one-way puzzles exist, then quantum bit commitments (and therefore EFI pairs, oblivious transfer and secure multiparty computation) exist. In particular, pure-state one-way state generators imply quantum bit commitments and secure multiparty computation. Thus quantum one-wayness, a natural quantum analogue of one-way functions, suffices for a large part of quantum cryptography, mirroring the classical fact that one-way functions imply commitments.

## Proof sketch

From a one-way puzzle construct an EFI-like pair: the distribution of puzzles together with a hardcore-type bit derived from the key versus an independent bit; one-wayness gives computational indistinguishability through a quantum Goldreich–Levin argument, while statistical farness follows from the inefficient verification. EFI then implies commitments, and commitments imply OT and MPC.

## Depends on

- [EFI pairs: efficient, statistically far, computationally indistinguishable states](efi-pairs.md)
- [One-way puzzles](one-way-puzzles.md)
- [One-way state generators](one-way-state-generators.md)
- [Quantum bit commitments in canonical form](quantum-bit-commitments.md)

## Proof depends on

- [One-way state generators with pure outputs yield one-way puzzles via shadow tomography](owsg-to-one-way-puzzles.md)
- [EFI pairs are equivalent to quantum commitments, oblivious transfer and secure computation](efi-equivalences.md)

## Sources

- Dakshita Khurana, Kabir Tomer, "Commitments from Quantum One-Wayness", STOC (2024), arXiv:2310.11526.
