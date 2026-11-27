# Göös–Kamath–Robere–Sokolov: PPA^dt is characterized by Nullstellensatz degree over F2

For every unsatisfiable $k$-CNF formula $F$ with $k$ constant, the $\mathbb F_2$-Nullstellensatz degree of $F$ equals $\Theta(\mathsf{PPA}^{dt}(S(F)))$; in the size-plus-degree measure, $\mathsf{PPA}^{dt}(S(F))=\Theta(\mathbb F_2\text{-}\mathrm{NS}(F))$, and the analogous statement $\mathsf{PPA}_p^{dt}(S(F))=\Theta(\mathbb F_p\text{-}\mathrm{NS}(F))$ holds for every prime $p$. In communication complexity, the analogue of PPA captures monotone span programs over $\mathbb F_2$, alongside the classical facts that communication FP captures formulas and communication PLS captures circuits.

## Proof sketch

Easy direction: a low-depth LEAF formulation yields a low-degree $\mathbb F_2$-NS refutation by summing, over all nodes, the parity of the degree as a polynomial of the queried bits; every node of odd degree other than the designated one is witnessed by a falsified clause, so the sum collapses to the identity $1=\sum_ip_i\overline{C_i}$ over $\mathbb F_2$. Hard direction: expand an NS refutation into monomials with multiplicity and pair up cancelling copies by a matching computable with few queries, so that unpaired monomials are exactly clause witnesses, giving a LEAF instance.

## Depends on

- [The false-clause search problem S(F) of an unsatisfiable CNF and its universality for TFNP^dt](false-clause-search-problem.md)
- [Unary Nullstellensatz and unary Sherali–Adams refutations of CNF formulas](unary-nullstellensatz-and-unary-sherali-adams.md)
- [Query total search problems TFNP^dt, decision-tree formulations and the black-box classes](query-tfnp-and-formulations.md)

## Sources

- Mika Göös, Pritish Kamath, Robert Robere and Dmitry Sokolov, "Adventures in Monotone Complexity and TFNP", ITCS (2019), ECCC TR18-163.
- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
