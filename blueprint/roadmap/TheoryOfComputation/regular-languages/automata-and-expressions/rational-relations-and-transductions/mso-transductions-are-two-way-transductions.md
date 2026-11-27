# MSO-definable string transductions are exactly the deterministic two-way transductions

A string transduction is [MSO-definable](two-way-transducers-and-mso-transductions.md) if and only if it is realized by a deterministic two-way finite state
transducer: $\mathrm{MSOS} = \mathrm{2DGSM}$ (Engelfriet and Hoogeboom). The nondeterministic MSO-definable transductions are the compositions of a
marked relabelling (a word $w$ is mapped to $\vdash w \dashv$ and each letter is then relabelled nondeterministically) with a deterministic two-way transduction,
$\mathrm{NMSOS} = \mathrm{MREL} \circ \mathrm{2DGSM}$, and equivalently the compositions of two nondeterministic two-way transducers with the *finite visit property* (for some $k$,
every pair of the transduction has a computation that visits each input position at most $k$ times), $\mathrm{NMSOS} = \mathrm{2NGSM}_{\mathrm{fin}} \circ \mathrm{2NGSM}_{\mathrm{fin}}$.
Together with the closure of MSO transductions under composition, the theorem shows that the deterministic two-way transductions preserve regularity under
inverse images, by Büchi's theorem.

## Depends on

- [Two-way transducers and MSO-definable string transductions](two-way-transducers-and-mso-transductions.md)

## Proof depends on

- [Büchi–Elgot–Trakhtenbrot theorem](../../../omega-automata-and-games/logic-and-tree-automata/buchielgottrakhtenbrot-theorem.md)

## Expansion

This page becomes ready once:

- The closure of deterministic two-way transductions under composition (Chytil and Jákl; Proposition 4 of the cited report), used in the proof (proof prerequisite; not yet stated)
- The closure of MSO graph transductions under composition and of MSO-definable graph languages under inverse MSO transductions (Courcelle; Proposition 12 of the cited report), used in the proof (proof prerequisite; not yet stated)

## Sources

- J. Engelfriet and H. J. Hoogeboom, "MSO definable string transductions and two-way finite-state transducers", *ACM Transactions on Computational Logic* 2(2), 2001; numbering of the technical report version, Leiden University TR 98-13, arXiv:cs/9906007: the abstract, Theorem 23 ($\mathrm{MSOS} = \mathrm{2DGSM}$) with its proof, Section 5, the definition of MREL before Theorem 30, Theorem 32 ($\mathrm{NMSOS} = \mathrm{MREL} \circ \mathrm{2DGSM}$), Section 6.1 (the finite visit property) and Theorem 37 ($\mathrm{NMSOS} = \mathrm{2NGSM}_{\mathrm{fin}} \circ \mathrm{2NGSM}_{\mathrm{fin}}$).
