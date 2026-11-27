# P is contained in BPP

Every decision problem decidable in deterministic polynomial time belongs to BPP: $\mathsf{P} \subseteq \mathsf{BPP}$.

## Proof sketch

A deterministic polynomial-time decider, used as a verifier that ignores its random string, accepts every member with probability $1$ and every non-member with probability $0$.

## Depends on

- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Expansion

This page becomes ready once:

- Closure of polynomial-time functions under composition, to compose that projection with the deterministic decider (proof prerequisite; link a matching result or state it before readiness)
- The projection of a pair of bitstrings to its first component is polynomial-time computable (proof prerequisite; not yet stated)

## Sources

- Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Section 7.8 ("We know that P ⊆ BPP ⊆ P/poly").
