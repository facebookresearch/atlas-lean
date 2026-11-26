# The false-clause search problem S(F) of an unsatisfiable CNF and its universality for TFNP^dt

For an unsatisfiable CNF $F=C_1\wedge\dots\wedge C_m$ over $n$ variables, the **false-clause search problem** is

$$
S(F)=\{(x,i)\in\{0,1\}^n\times[m]:\ C_i(x)=0\}:
$$

given an assignment, find a falsified clause. If the clauses have width $\mathrm{poly}(\log n)$ then $S(F)\in\mathsf{TFNP}^{dt}$. Conversely every $R\in\mathsf{TFNP}^{dt}$ with verifiers $T_o$ equals $S(F)$ up to relabelling for $F=\bigwedge_{o}\neg T_o(x)$, where each $\neg T_o$ is written as a CNF with one clause per accepting leaf, of width at most the depth of $T_o$. For a propositional proof system $\mathcal P$ write

$$
\mathcal P(F)=\min_{\Pi}\bigl(\log\mathrm{size}(\Pi)+\deg(\Pi)\bigr),
$$

the minimum over $\mathcal P$-refutations $\Pi$ of $F$, where degree means width for Resolution-like systems and depth for tree-like Resolution. A **characterization** of a class $X$ by a system $\mathcal P$ is an equality $X^{dt}(S(F))=\Theta(\mathcal P(F))$ for all unsatisfiable $F$.

## Depends on

- [Query total search problems TFNP^dt, decision-tree formulations and the black-box classes](query-tfnp-and-formulations.md)
- [Resolution refutation](../../../../Logic/propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Cook–Reckhow propositional proof systems](../../../../Logic/propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
- Mika Göös, Pritish Kamath, Robert Robere and Dmitry Sokolov, "Adventures in Monotone Complexity and TFNP", ITCS (2019), ECCC TR18-163.
