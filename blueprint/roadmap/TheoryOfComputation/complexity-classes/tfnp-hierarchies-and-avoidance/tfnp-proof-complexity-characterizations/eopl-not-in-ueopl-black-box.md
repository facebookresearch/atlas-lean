# EOPL^dt ⊄ UEOPL^dt: unique end of potential line is strictly weaker in the black-box model

$\mathsf{EOPL}^{dt}\not\subseteq\mathsf{UEOPL}^{dt}$; hence there is an oracle relative to which $\mathsf{EOPL}\not\subseteq\mathsf{UEOPL}$, confirming in the black-box setting the conjecture of Fearnley, Gordon, Mehta and Savani that the inclusion $\mathsf{UEOPL}\subseteq\mathsf{EOPL}$ is proper.

## Proof sketch

Every glueable problem in $\mathsf{UEOPL}^{dt}$ lies in $\mathsf{FP}^{dt}$: fixing a UNIQUE-EOPL formulation completed for glueability, each row of the grid contains at most one good node (active with a non-witnessing leaf), since two would form a (two parallel lines) solution certified by a non-witnessing union, and binary search over rows then finds a solution with polylogarithmically many queries. END-OF-POTENTIAL-LINE with explicit activity bits is glueable, and it is known that $\mathsf{EOPL}^{dt}\ne\mathsf{FP}^{dt}$, so $\mathsf{EOPL}^{dt}\subseteq\mathsf{UEOPL}^{dt}$ is impossible.

## Depends on

- [Query total search problems TFNP^dt, decision-tree formulations and the black-box classes](query-tfnp-and-formulations.md)
- [UEOPL ⊆ EOPL ⊆ CLS = PPAD ∩ PLS](../unique-end-of-potential-line/ueopl-subset-eopl-subset-cls.md)
- [UNIQUE-EOPL, the class UEOPL and PromiseUEOPL: one potential line certified by violation solutions](../unique-end-of-potential-line/unique-eopl-and-ueopl.md)

## Proof depends on

- [PLS^dt ⊄ PPP^dt via glueability, settling the last oracle question among the 1990s TFNP classes](pls-not-in-ppp-black-box.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", ICALP (2019), arXiv:1811.03841.
