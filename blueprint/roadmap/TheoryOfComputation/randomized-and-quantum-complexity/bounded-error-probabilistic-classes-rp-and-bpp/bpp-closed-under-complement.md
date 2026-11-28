# BPP is closed under complement

A decision problem belongs to BPP if and only if its complement belongs to BPP, that is $\mathsf{BPP} = \mathsf{coBPP}$.

## Proof sketch

In the definition of BPP the acceptance thresholds, at least $2/3$ on members and at most $1/3$ on non-members, are symmetric, so negating the output of the polynomial-time verifier gives a verifier for the complement.

## Depends on

- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Expansion

This page becomes ready once:

- The negation of a polynomial-time computable Boolean function is polynomial-time computable (proof prerequisite; not yet stated)

## Sources

- Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Section 7.7, proof of Theorem 7.18 ("BPP is closed under complementation (i.e., BPP = coBPP)").
