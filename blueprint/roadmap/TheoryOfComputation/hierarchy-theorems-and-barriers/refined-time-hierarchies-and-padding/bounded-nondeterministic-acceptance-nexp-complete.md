# Bounded nondeterministic acceptance is NEXP-complete

Let $\mathrm{NBA}$ be the language of triples $\langle M,x,t\rangle$ (with $t$ written in binary) for which there exists a certificate $c$ with $|c|\le t$ such that the universal machine running $M$ on $\langle x,c\rangle$ halts with output $1$ within $t$ steps. Then $\mathrm{NBA}$ is $\mathsf{NEXP}$-complete under polynomial-time many-one reductions, and $\mathsf{NEXP}=\mathsf{EXP}$ iff $\mathrm{NBA}\in\mathsf{EXP}$. Similarly the deterministic bounded-termination problem ($M$ halts on $x$ within $t$ steps, $t$ in binary) is in $\mathsf{E}$, is outside $\mathsf{P}$, and is $\mathsf{EXP}$-complete.

## Proof sketch

Membership: guess $c$ and simulate for $t<2^{|t|}$ steps, which takes time $2^{O(n)}$ on inputs of length $n\ge|t|$. Hardness: a language decided by a verifier $V$ in time $2^{n^k}$ maps $x$ to $\langle V,x,2^{|x|^k}\rangle$, whose binary bound has polynomial length. The deterministic version is in $\mathsf{E}$ by clocked universal simulation, $\mathsf{EXP}$-hard by the analogous reduction $x\mapsto\langle M,x,2^{|x|^k}\rangle$, and outside $\mathsf{P}$ because $\mathsf{P}\ne\mathsf{EXP}$ by the time hierarchy theorem (Goldreich, Exercises 4.6–4.7).

## Depends on

- [The complexity class NEXP](../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [The class EXP](../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [The class E](../../complexity-classes/time-and-space-complexity-classes/e.md)

## Proof depends on

- [Deterministic time hierarchy: quadratic versus linear time](../time-hierarchy-theorem/time-hierarchy.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 2, Exercise 9 (published by Cambridge University Press, 2009).
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 3–5", 2007, Exercises 4.6–4.7 (published by Cambridge University Press, 2008).
