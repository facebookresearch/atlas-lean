# Hartmanis–Immerman–Sewelson: easy tally NP sets collapse NEXP to EXP

If every tally language in $\mathsf{NP}$ is in $\mathsf{P}$, then $\mathsf{EXP}=\mathsf{NEXP}$ and $\mathsf{E}=\mathsf{NE}$.

## Proof sketch

For $L\in\mathsf{NE}$, let $m_x$ be the number whose binary representation is $1x$ (so $x\mapsto m_x$ is injective and $m_x<2^{|x|+1}$) and consider the tally set $T_L=\{1^{m_x}: x\in L\}$, which is in $\mathsf{NP}$ because the unary length pays for the $2^{O(|x|)}$-time nondeterministic computation. If $T_L\in\mathsf{P}$, then $L$ is decided by writing $1^{m_x}$ and running the polynomial-time algorithm, in time $2^{O(|x|)}$, so $\mathsf{E}=\mathsf{NE}$; padding then lifts $\mathsf{E}=\mathsf{NE}$ to $\mathsf{EXP}=\mathsf{NEXP}$.

## Depends on

- [Tally languages](../../complexity-classes/structural-complexity/advice-sparse-and-selective-sets/tally-languages.md)
- [The complexity class NEXP](../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [The class EXP](../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [The class E](../../complexity-classes/time-and-space-complexity-classes/e.md)

## Proof depends on

- [Padding: upward translation of class collapses](padding-translates-collapses.md)

## Sources

- Juris Hartmanis, Neil Immerman and Vivian Sewelson, "Sparse Sets in NP-P: EXPTIME versus NEXPTIME", Information and Control 65(2–3), 158–181, 1985.
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 2, Exercise 23 (published by Cambridge University Press, 2009).
