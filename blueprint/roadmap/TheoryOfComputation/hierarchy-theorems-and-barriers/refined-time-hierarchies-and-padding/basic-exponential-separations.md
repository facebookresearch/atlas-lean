# NP ⊊ NEXP, P ⊊ E ⊊ EXP and PSPACE ⊊ EXPSPACE

On binary words: $\mathsf{P}\subsetneq\mathsf{E}\subsetneq\mathsf{EXP}$, $\mathsf{NP}\subsetneq\mathsf{NEXP}$, and $\mathsf{PSPACE}\subsetneq\mathsf{EXPSPACE}$. Moreover $\mathsf{E}$ is not closed under polynomial-time many-one reductions, hence $\mathsf{E}\ne\mathsf{NP}$ and $\mathsf{E}\ne\mathsf{PSPACE}$.

## Proof sketch

The deterministic and nondeterministic time hierarchies and the space hierarchy separate the classes. For non-closure, pad a language of $\mathsf{DTIME}(2^{n^2})\setminus\mathsf{E}$ to quadratic length: the padded language lies in $\mathsf{E}$ and the original reduces to it.

## Depends on

- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The class E](../../complexity-classes/time-and-space-complexity-classes/e.md)
- [The class EXP](../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The complexity class NEXP](../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)
- [The class EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md)

## Proof depends on

- [Deterministic time hierarchy: quadratic versus linear time](../time-hierarchy-theorem/time-hierarchy.md)
- [Nondeterministic time hierarchy](../nondet-time-hierarchy.md)
- [Space hierarchy theorem for space-constructible bounds](../space-hierarchy-theorem/space-hierarchy-theorem-for-space-constructible.md)
- [Padding: upward translation of class collapses](padding-translates-collapses.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
- Ronald V. Book, "Comparing Complexity Classes", Journal of Computer and System Sciences 9(2), 1974.
