# The halting problem is NP-hard but not in NP

The language $\mathrm{HALT}=\{\langle M,x\rangle : M$ halts on $x\}$ is $\mathsf{NP}$-hard under polynomial-time many-one reductions, but it is not in $\mathsf{NP}$ (indeed undecidable), so it is not $\mathsf{NP}$-complete.

## Proof sketch

Bounded termination is $\mathsf{EXP}$-complete and $\mathsf{NP}\subseteq\mathsf{EXP}$; turning a decider for bounded termination into a machine that diverges on 'no' gives a fixed machine $M_0$ halting exactly on yes-instances, and $x\mapsto\langle M_0,x\rangle$ reduces every NP language to HALT.

## Depends on

- [Halting set](../../degrees-and-hierarchies/turing-reducibility/halting-set.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Bounded nondeterministic acceptance is NEXP-complete](../../hierarchy-theorems-and-barriers/refined-time-hierarchies-and-padding/bounded-nondeterministic-acceptance-nexp-complete.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 2, Exercise 3.
