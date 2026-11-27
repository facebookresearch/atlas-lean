# PLS^dt ⊄ PPP^dt via glueability, settling the last oracle question among the 1990s TFNP classes

$\mathsf{PLS}^{dt}\not\subseteq\mathsf{PPP}^{dt}$, hence $\mathsf{PLS}^{\mathcal O}\not\subseteq\mathsf{PPP}^{\mathcal O}$ for some oracle. Together with earlier work this completes the black-box picture of inclusions and separations among PLS, PPAD, PPADS, PPA and PPP: every inclusion not implied by $\mathsf{PPAD}\subseteq\mathsf{PPADS}\subseteq\mathsf{PPP}$ and $\mathsf{PPAD}\subseteq\mathsf{PPA}$ fails relative to an oracle.

## Proof sketch

Call $R$ **glueable** if every low-depth partial assignment can be completed by a short decision tree so that any two consistent non-witnessing completed partial assignments have a non-witnessing union on which $R$ still needs many queries. Key lemma: a glueable problem in $\mathsf{PPP}^{dt}$ lies in $\mathsf{PPADS}^{dt}$, because glueability lets decision trees compute reverse pointers for the holes of a PIGEON formulation, giving a formulation of the PPADS-complete Reversible-Pigeon problem. SINK-OF-DAG, with an explicit activity bit per node, is glueable (an adversary pushes any active path below the queried rows). So $\mathsf{PLS}^{dt}\subseteq\mathsf{PPP}^{dt}$ would contradict $\mathsf{PLS}^{dt}\not\subseteq\mathsf{PPADS}^{dt}$; Bonacina and Thapen independently derived the result from the same separation.

## Depends on

- [Query total search problems TFNP^dt, decision-tree formulations and the black-box classes](query-tfnp-and-formulations.md)

## Proof depends on

- [Black-box separations PLS^dt ⊄ PPADS^dt and SOPL^dt ⊄ PPA^dt](pls-not-in-ppads-and-sopl-not-in-ppa-black-box.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
