# Hartmanis–Immerman–Sewelson: easy tally NP sets collapse NEXP to EXP

If every tally language in $\mathsf{NP}$ is in $\mathsf{P}$, then $\mathsf{EXP}=\mathsf{NEXP}$ and $\mathsf{E}=\mathsf{NE}$.

## Proof sketch

For $L\in\mathsf{NE}$, write $x$ in binary as a number $m_x$ and consider the tally set $\{1^{m_x}: x\in L\}$, which is in $\mathsf{NP}$ because the unary length pays for the exponential-time verification. If it is in $\mathsf{P}$, the deterministic algorithm on $1^{m_x}$ runs in time $2^{O(|x|)}$.

## Depends on

- [Tally languages](../../complexity-classes/advice-sparse-and-selective-sets/tally-languages.md)
- [The complexity class NEXP](../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [The class EXP](../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [The class E](../../complexity-classes/time-and-space-complexity-classes/e.md)

## Proof depends on

- [Padding: upward translation of class collapses](padding-translates-collapses.md)

## Sources

- Juris Hartmanis, Neil Immerman and Vivian Sewelson, "Sparse Sets in NP-P: EXPTIME versus NEXPTIME", Information and Control 65(2–3), 1985.
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 2, Exercise 23.
