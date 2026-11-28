# Characterizing a proof system by a black-box TFNP problem

A black-box TFNP problem characterizes a proof system when the false-clause search problems of CNF formulas that reduce to it by shallow decision trees are exactly those of the formulas with polylogarithmic proof complexity, measured as degree plus logarithm of size.

**Setting.** Total query search problems, the class $\mathsf{TFNP}^{dt}$, decision-tree formulations (reductions) of complexity $\log m + d$, the measure $R^{dt}(Q)$ and the class $R^{dt}$ of problems $Q \in \mathsf{TFNP}^{dt}$ with $R^{dt}(Q) = \mathrm{polylog}(n)$ are as on [query total search problems](query-tfnp-and-formulations.md). The false-clause search problem $S_F$ of an unsatisfiable CNF $F$ and the proof complexity measure

$$
P(F) = \min\{\deg(\Pi) + \log \mathrm{size}(\Pi) : \Pi \text{ is a } P\text{-proof of } F\}
$$

of a proof system $P$ with a degree measure (polynomial degree for Nullstellensatz, Polynomial Calculus and Sherali-Adams, clause width for resolution) are as on [the false-clause search problem](false-clause-search-problem.md).

**Definition.** A problem $R \in \mathsf{TFNP}^{dt}$ **characterizes** a proof system $P$ if

$$
R^{dt} = \{S_F : P(F) = \mathrm{polylog}(n)\},
$$

where $n$ is the number of variables of $F$.

## Expansion

This polylogarithmic notion is weaker than the $\Theta$ form $R^{dt}(S_F) = \Theta(P(F))$ used on the false-clause page: the $\Theta$ form implies it. Every $R \in \mathsf{TFNP}^{dt}$ with verifier trees $T_i^o$ ($i \in O$) on its $n$ input bits is equivalent to $S_F$ for the unsatisfiable CNF $F = \bigwedge_{i \in O} \neg T_i^o$ in those $n$ input variables, with one sub-CNF $\neg T_i^o$ for each solution $i \in O$; the source's Claim 1 prints "on $|O|$-many variables", but its own proof builds this formula over the input variables. Hence a TFNP subclass defined by a complete problem corresponds to a proof system in this sense.

The source recalls known instances: $\mathsf{FP}^{dt}$ is tree-like resolution, [$\mathsf{PLS}^{dt}$ is resolution](pls-dt-characterized-by-resolution.md), [$\mathsf{PPA}^{dt}$ is $\mathbb{F}_2$-Nullstellensatz and $\mathsf{PPA}_q^{dt}$ is $\mathbb{F}_q$-Nullstellensatz](ppa-dt-characterized-by-f2-nullstellensatz.md), and [$\mathsf{PPAD}^{dt}$, $\mathsf{PPADS}^{dt}$, $\mathsf{SOPL}^{dt}$ and $\mathsf{EOPL}^{dt}$ are unary Nullstellensatz, unary Sherali-Adams, RevRes and RevResT](ppad-ppads-sopl-eopl-proof-system-characterizations.md), all in the $\Theta$ form. The source's introductory list swaps the PPAD and PPADS entries; its own later text pairs unary Nullstellensatz with END-OF-LINE and unary Sherali-Adams with SINK-OF-LINE, as stated here. The measure $\deg + \log \mathrm{size}$ is the parameter that query-to-communication lifting theorems transfer to monotone circuit models.

## Depends on

- [Query total search problems TFNP^dt, decision-tree formulations and the black-box classes](query-tfnp-and-formulations.md)
- [The false-clause search problem S(F) of an unsatisfiable CNF and its universality for TFNP^dt](false-clause-search-problem.md)
- [Cook-Reckhow propositional proof systems](../../../../Logic/propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Sam Buss, Noah Fleming, Russell Impagliazzo, "TFNP Characterizations of Proof Systems and Monotone Circuits", *14th Innovations in Theoretical Computer Science Conference (ITCS 2023)*, LIPIcs, 2023, doi:10.4230/LIPIcs.ITCS.2023.30 (Section 2: the definition of characterization; Claim 1 and its proof; the unary Polynomial Calculus discussion for the END-OF-LINE pairing).
- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere, Ran Tao, "Separations in Proof Complexity and TFNP", *Journal of the ACM*, 2024, arXiv:2205.02168 (characterizations of PPADS, PPAD and SOPL by unary Sherali-Adams, unary Nullstellensatz and reversible resolution).
