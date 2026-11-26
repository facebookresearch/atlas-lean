# One-way state generators with pure outputs yield one-way puzzles via shadow tomography

Let $(\mathsf{KeyGen},\mathsf{StateGen},\mathsf{Ver})$ be a pure-state OWSG. Define a one-way puzzle whose sampler draws $k$, prepares polynomially many copies of $|\phi_k\rangle$, and outputs as the puzzle $s$ the classical outcomes of efficient (randomized Clifford) classical-shadow measurements on these copies, with key $k$; verification accepts $(s,k')$ if the classical shadow estimates the fidelity of the measured state with $|\phi_{k'}\rangle$ as large. Then this is a one-way puzzle: honest pairs verify with high probability by the accuracy of classical shadows, and an adversary solving puzzles from $s$ would break the OWSG given copies, since it can compute $s$ itself.

## Proof sketch

Classical shadows estimate $\langle\phi_{k'}|\rho|\phi_{k'}\rangle$ for all $k'$ simultaneously with polynomially many copies and accuracy $\epsilon$ with high probability (union bound over $2^{\lambda}$ keys, logarithmic dependence). A solver for the puzzle produces $k'$ with high estimated fidelity, which by accuracy implies high true fidelity, contradicting OWSG security; the verification predicate is inefficient only because estimation over the full puzzle is allowed to be expensive.

## Depends on

- [One-way puzzles](one-way-puzzles.md)
- [One-way state generators](one-way-state-generators.md)

## Sources

- Dakshita Khurana, Kabir Tomer, "Commitments from Quantum One-Wayness", STOC (2024), arXiv:2310.11526.
