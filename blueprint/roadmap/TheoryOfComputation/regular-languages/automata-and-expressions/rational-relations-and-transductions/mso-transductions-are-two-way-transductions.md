# MSO-definable string transductions are exactly the deterministic two-way transductions

A string transduction is [MSO-definable](two-way-transducers-and-mso-transductions.md) if and only if it is realized by a deterministic two-way finite state
transducer: $\mathrm{MSOS} = \mathrm{2DGSM}$ (Engelfriet and Hoogeboom). The nondeterministic MSO-definable transductions are the compositions of a
marking relation with a deterministic two-way transduction, $\mathrm{NMSOS} = \mathrm{MREL} \circ \mathrm{2DGSM}$, equivalently compositions of two nondeterministic two-way
transducers with the finite visit property. As a consequence the deterministic two-way transductions are closed under composition and
preserve regularity under inverse images, by Büchi's theorem.

## Depends on

- [Two-way transducers and MSO-definable string transductions](two-way-transducers-and-mso-transductions.md)

## Proof depends on

- [Büchi–Elgot–Trakhtenbrot theorem](../../../omega-automata-and-games/logic-and-tree-automata/buchielgottrakhtenbrot-theorem.md)

## Sources

- J. Engelfriet and H. J. Hoogeboom, "MSO definable string transductions and two-way finite-state transducers", *ACM Transactions on Computational Logic* 2(2), 2001; numbering of the technical report version, Leiden University TR 98-13, arXiv:cs/9906007: the abstract, Theorem 23 ($\mathrm{MSOS} = \mathrm{2DGSM}$) with its proof, and Theorem 32 ($\mathrm{NMSOS} = \mathrm{MREL} \circ \mathrm{2DGSM}$).
