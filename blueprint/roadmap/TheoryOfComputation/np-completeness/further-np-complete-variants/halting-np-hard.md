# The halting problem is NP-hard but not in NP

The language $\mathrm{HALT}=\{\langle M,x\rangle : M$ halts on $x\}$ is $\mathsf{NP}$-hard under polynomial-time many-one reductions, but it is not in $\mathsf{NP}$ (indeed undecidable), so it is not $\mathsf{NP}$-complete.

## Proof sketch

Let $L\in\mathsf{NP}$ have a polynomial-time verifier $V$ with certificates of length at most $p(|x|)$. The fixed machine $M_L$ that, on input $x$, tries every certificate of length at most $p(|x|)$, halts as soon as $V$ accepts one and otherwise loops forever, halts exactly on $L$; so $x\mapsto\langle M_L,x\rangle$ is a polynomial-time reduction from $L$ to $\mathrm{HALT}$. $\mathrm{HALT}$ is undecidable, while every language in $\mathsf{NP}$ is decidable.

## Depends on

- [Halting set](../../degrees-and-hierarchies/turing-reducibility/halting-set.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 2, Exercise 3 (published by Cambridge University Press, 2009).
