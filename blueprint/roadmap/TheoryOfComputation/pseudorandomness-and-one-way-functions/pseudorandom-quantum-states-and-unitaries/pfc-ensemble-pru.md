# Pseudorandom unitaries from the PFC ensemble and one-way functions

Assuming quantum-secure one-way functions, the ensemble $U=P\,F\,C$, where $P$ is a pseudorandom permutation of computational basis states, $F$ a pseudorandom binary phase function (diagonal $\pm 1$ unitary), and $C$ a random Clifford (or other 2-design), is a pseudorandom unitary family secure against adaptive adversaries; with a symmetrized variant it is a strong PRU (secure even given inverse queries). Moreover, replacing the pseudorandom permutation and phase by $t$-wise independent ones yields $\epsilon$-approximate unitary $t$-designs of circuit depth linear in $n$ (and polylogarithmic in $t/\epsilon$ factors). Hence PRUs exist if and only if (up to the classical-to-quantum gap) quantum-secure one-way functions exist in the black-box sense, and Haar-random unitaries can be efficiently simulated.

## Proof sketch

First show non-adaptive security: after the Clifford twirl, $t$ parallel copies of $PF$ applied to a state supported on distinct tuples act like a random permutation with random signs, whose moments match Haar moments up to $O(t^{2}/2^{n})$. For adaptive security, use a path-recording purification of the random permutation and phase oracles that records the queried paths, and show that the adversary's view is close to that with a purified Haar-random unitary.

## Depends on

- [Pseudorandom unitaries](pseudorandom-unitaries.md)
- [Asymptotic PRF security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-functions/prfsecure.md)

## Proof depends on

- [Pseudorandom states from quantum-secure pseudorandom functions](random-phase-prs.md)

## Sources

- Tony Metger, Alexander Poremba, Makrand Sinha, Henry Yuen, "Simple Constructions of Linear-Depth t-Designs and Pseudorandom Unitaries", FOCS (2024), arXiv:2404.12647.
- Fermi Ma, Hsin-Yuan Huang, "How to Construct Random Unitaries", STOC (2025), IACR ePrint 2024/1652.
