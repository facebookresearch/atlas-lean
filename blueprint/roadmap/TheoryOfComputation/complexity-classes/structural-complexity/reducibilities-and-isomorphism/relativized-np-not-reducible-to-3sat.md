# An oracle language in NP^A not polynomial-time reducible to 3SAT

There is an oracle $A$ and a language $L\in\mathsf{NP}^{A}$ that is not polynomial-time many-one reducible to $\mathrm{3SAT}$. So the Cook–Levin theorem, in the form that every $\mathsf{NP}$ language reduces to $\mathrm{3SAT}$, does not hold relative to every oracle.

## Proof sketch

Derived here (not stated in the main text of the cited source; its Exercise 6 asks for the stronger form): for every fixed target language $T$ (for instance $T=\mathrm{3SAT}$) there is an oracle $B$ such that the unary language $L_B=\{1^n:\exists y\in B,\ |y|=n\}\in\mathsf{NP}^{B}$ has no many-one reduction to $T$ computable in polynomial time even with access to $B$. Diagonalize over oracle reductions $R_i$ with clocks $n^i$: choose $n$ larger than all lengths queried so far, run $R_i^B(1^n)$, and add a string of length $n$ to $B$ not queried by it exactly when $R_i$'s output lies outside $T$, so $R_i$ errs on $1^n$. Reductions without oracle access are a special case.

## Depends on

- [NP relative to an oracle](../../time-and-space-complexity-classes/npwith-oracle.md)
- [Polynomial-time many-one reduction](../../../np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)
- [The 3SAT decision problem](../../../np-completeness/satisfiability/3-satisfiability/sat3-dec.md)

## Proof depends on

- [Polynomial time with an oracle](../../time-and-space-complexity-classes/pwith-oracle.md)
- [Baker-Gill-Solovay: oracles separate and collapse P vs NP](../../../hierarchy-theorems-and-barriers/relativization-and-oracle-separations/baker-gill-solovay.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Section 3.5, p3.8, the paragraph after the proof of Theorem 3.9 ("It is not true for a general oracle A that every language L ∈ NP^A is polynomial-time reducible to 3SAT"), with Chapter 3, Exercise 6.
