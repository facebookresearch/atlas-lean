# SYM ∘ AND circuits

A *$\mathrm{SYM}\circ\mathrm{AND}$ circuit* on inputs $x_1,\dots,x_n$ consists of a finite multiset of AND gates, each reading a set $S\subseteq\{1,\dots,n\}$ of input positions, below one symmetric output gate given by a function $\sigma:\mathbb{N}\to\{0,1\}$; on input $x$ it outputs $\sigma\bigl(|\{\text{AND gates } S:\ x_i=1\ \forall i\in S\}|\bigr)$. Its *size* is the number of AND gates and its *fan-in* is the largest $|S|$.

## Depends on

- [Straight-line programs and circuits over a basis](../../circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- Richard Beigel, Jun Tarui, "On ACC", Computational Complexity 4, 1994.
- Ryan Williams, "Nonuniform ACC Circuit Lower Bounds", Journal of the ACM 61(1), Article 2, 2014 (Section 2, SYM+ circuits).
