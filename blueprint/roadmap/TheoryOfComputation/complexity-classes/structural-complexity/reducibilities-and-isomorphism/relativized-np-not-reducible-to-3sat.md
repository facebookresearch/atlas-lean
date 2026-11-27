# An oracle language in NP^B with no oracle-aided reduction to 3SAT

For every fixed target language $T$ (for instance $T=\mathrm{3SAT}$), there is an oracle $B$ and a unary language $L_B\in\mathsf{NP}^{B}$ that has no many-one reduction to $T$ computable in polynomial time with access to $B$. Hence the relativized statement '3SAT is $\mathsf{NP}^B$-complete under $\mathsf{P}^B$ reductions' fails for some oracle, so the Cook–Levin theorem does not relativize in this form.

## Proof sketch

Let $L_B=\{1^n:\exists y\in B,\ |y|=n\}$. Diagonalize over oracle reductions $R_i$ with clocks $n^i$: choose $n$ larger than all lengths queried so far, run $R_i^B(1^n)$, and add a string of length $n$ to $B$ not queried by it exactly when $R_i$'s output lies outside $T$, so $R_i$ errs on $1^n$.

## Depends on

- [NP relative to an oracle](../../time-and-space-complexity-classes/npwith-oracle.md)
- [Polynomial time with an oracle](../../time-and-space-complexity-classes/pwith-oracle.md)

## Proof depends on

- [Baker-Gill-Solovay: oracles separate and collapse P vs NP](../../../hierarchy-theorems-and-barriers/relativization-and-oracle-separations/baker-gill-solovay.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 3, Exercise 6.
